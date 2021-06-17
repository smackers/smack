import re
import functools
import shutil
import subprocess
import json


def reformat_assignment(line):
    '''Transform assignment RHS values'''

    def repl(m):
        val = m.group(1)
        if 'bv' in val:
            return m.group(2) + 'UL'
        else:
            sig_size = int(m.group(7))
            exp_size = int(m.group(8))
            # assume we can only handle double
            if sig_size > 53 or exp_size > 11:
                return m.group()

            sign_val = -1 if m.group(3) != '' else 1
            sig_val = m.group(4)
            exp_sign_val = -1 if m.group(5) != '' else 1
            # note that the exponent base is 16
            exp_val = 2**(4 * exp_sign_val * int(m.group(6)))
            return str(sign_val * float.fromhex(sig_val) * exp_val)

    # Boogie FP const grammar: (-)0x[sig]e[exp]f[sigSize]e[expSize], where
    # sig = hexdigit {hexdigit} '.' hexdigit {hexdigit}
    # exp = digit {digit}
    # sigSize = digit {digit}
    # expSize = digit {digit}
    return re.sub(
        (r'((\d+)bv\d+|(-?)0x([0-9a-fA-F]+\.[0-9a-fA-F]+)e(-?)'
         r'(\d+)f(\d+)e(\d+))'),
        repl,
        line.strip())


def demangle(func):
    '''Demangle C++/Rust function names'''

    def demangle_with(func, tool):
        if shutil.which(tool):
            p = subprocess.Popen(
                tool,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE)
            out, _ = p.communicate(input=func.encode())
            return out.decode()
        return func
    return functools.reduce(demangle_with, ['cxxfilt', 'rustfilt'], func)


def transform(info):
    '''Transform an error trace line'''

    if info.startswith('CALL') or info.startswith('RETURN from'):
        tokens = info.split()
        tokens[-1] = demangle(tokens[-1])
        return ' '.join(tokens)
    elif '=' in info:
        tokens = info.split('=')
        lhs = tokens[0].strip()
        rhs = tokens[1].strip()
        return demangle(lhs) + ' = ' + reformat_assignment(rhs)
    else:
        return info


def error_trace(verifier_output, verifier):
    '''Generate string error trace.'''
    from .top import VResult

    def merger(traces, trace):
        if len(traces) == 0:
            return [trace]
        last_trace = traces[-1]
        if (last_trace['file'] == trace['file']
            and last_trace['line'] == trace['line']
                and last_trace['column'] == trace['column']):
            if len(trace['description']) != 0:
                if len(last_trace['description']) == 0:
                    last_trace['description'] = trace['description']
                else:
                    last_trace['description'] += (', ' + trace['description'])
            return traces
        else:
            return traces + [trace]

    traces = json_output(VResult.ERROR, verifier_output, verifier)['traces']
    output = '\n'.join(
        map(
            lambda trace: '{0}({1},{2}): {3}'.format(
                trace['file'],
                trace['line'],
                trace['column'],
                trace['description']), functools.reduce(merger, traces, [])))
    return output


def smackdOutput(result, output, verifier):
    return json.dumps(json_output(result, output, verifier))


def json_output(result, output, verifier):
    '''Convert error traces into JSON format'''

    from .top import VResult

    if not (result is VResult.VERIFIED or result in VResult.ERROR):
        return

    FILENAME = r'[\w#$~%.\/-]+'
    failsAt = None

    if result is VResult.VERIFIED:
        json_data = {
            'verifier': verifier,
            'passed?': True
        }
    elif verifier == 'boogie':
        traces = []
        traceP = re.compile(r"(\s*)(%s)\((\d+),\d+\):" % FILENAME)
        steps = re.findall(traceP, output)
        for step in steps:
            if re.match('.*[.]bpl$', step[1]):
                line_no = int(step[2])
                with open(step[1]) as f:
                    for ln in f.read().splitlines(True)[line_no:line_no + 10]:
                        src = re.match(
                            r".*{:sourceloc \"(%s)\", (\d+), (\d+)}" %
                            FILENAME, ln)
                        if src:
                            traces.append(
                                {'file': src.group(1),
                                 'line': src.group(2),
                                 'column': src.group(3),
                                 'description': ''})
                            break
    elif verifier == 'corral':
        traces = []
        traceP = re.compile(
            ('('
             + FILENAME
             + r')\((\d+),(\d+)\): Trace: Thread=(\d+)\s+\((.*(;\n)?.*)\)'))
        raw_data = re.findall(traceP, output)
        for step in raw_data:
            file_name = step[0]
            line_num = step[1]
            col_num = step[2]
            thread_id = step[3]
            description = step[4]
            if 'ASSERTION FAILS' in description:
                description = re.sub('ASSERTION FAILS.*;\n', '', description)
                failsAt = {
                    'file': file_name,
                    'line': line_num,
                    'column': col_num,
                    'description': ''}

            for token in description.split(','):
                token = token.strip()
                if re.search(
                  (r'((CALL|RETURN from)\s+(\$|__SMACK))|'
                   r'Done|ASSERTION'), token) is not None:
                    continue
                traces.append(
                    {'threadid': thread_id,
                     'file': file_name,
                     'line': line_num,
                     'column': col_num,
                     'description': token,
                     'assumption': transform(token) if '=' in token else ''})
    json_data = {
            'verifier': verifier,
            'passed?': False,
            'failsAt': failsAt,
            'threadCount': 1,
            'traces': traces
    }
    return json_data
