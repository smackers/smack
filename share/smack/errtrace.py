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

    info = info.strip()
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


def corral_error_step(step):
    '''Produce an error trace step based on a line of Corral error trace'''

    m = re.match(r'([^\s]*)\s+Trace:\s+(Thread=\d+)\s+\((.*)[\)|;]', step)
    if m:
        path = m.group(1)
        tid = m.group(2)
        info = ','.join(map(transform,
                            [x for x in m.group(3).split(',') if not
                                re.search(
                                    (r'((CALL|RETURN from)\s+(\$|__SMACK))|'
                                     r'Done|ASSERTION'), x)]))
        return '{0}\t{1}  {2}'.format(path, tid, info)
    else:
        return step


def error_step(step):
    '''Produce an error trace step based on a line of verifier output'''

    FILENAME = r'[\w#$~%.\/-]*'
    step = re.match(r"(\s*)(%s)\((\d+),\d+\): (.*)" % FILENAME, step)
    if step:
        if re.match('.*[.]bpl$', step.group(2)):
            line_no = int(step.group(3))
            message = step.group(4)
            if re.match(r'.*\$bb\d+.*', message):
                message = ""
            with open(step.group(2)) as f:
                for line in f.read().splitlines(True)[line_no:line_no + 10]:
                    src = re.match(
                        r".*{:sourceloc \"(%s)\", (\d+), (\d+)}" %
                        FILENAME, line)
                    if src:
                        return "%s%s(%s,%s): %s" % (step.group(1), src.group(
                            1), src.group(2), src.group(3), message)
        else:
            return corral_error_step(step.group(0))
    else:
        return None


def error_trace(verifier_output, args):
    '''Generate string error trace.'''

    trace = ""
    for line in verifier_output.splitlines(True):
        step = error_step(line)
        if step:
            m = re.match('(.*): [Ee]rror [A-Z0-9]+: (.*)', step)
            if m:
                trace += "%s: %s\nExecution trace:\n" % (
                    m.group(1), m.group(2))
            else:
                trace += ('' if step[0] == ' ' else '    ') + step + "\n"

    return trace


def smackdOutput(result, corralOutput):
    '''Convert error traces into JSON format'''

    from .top import VResult

    if not (result is VResult.VERIFIED or result in VResult.ERROR):
        return

    FILENAME = r'[\w#$~%.\/-]+'
    traceP = re.compile(
        ('('
         + FILENAME
         + r')\((\d+),(\d+)\): Trace: Thread=(\d+)\s+\((.*(;\n)?.*)\)'))
    # test1.i(223,16): Trace: Thread=1  (ASSERTION FAILS assert false;
    errorP = re.compile(
        ('('
         + FILENAME
         + r')\((\d+),(\d+)\): Trace: Thread=\d+\s+\(ASSERTION FAILS'))

    if result is VResult.VERIFIED:
        json_data = {
            'verifier': 'corral',
            'passed?': True
        }
    else:
        traces = []
        raw_data = re.findall(traceP, corralOutput)
        for t in raw_data:
            file_name = t[0]
            line_num = t[1]
            col_num = t[2]
            thread_id = t[3]
            description = t[4]
            for token in description.split(','):
                traces.append(
                    {'threadid': thread_id,
                     'file': file_name,
                     'line': line_num,
                     'column': col_num,
                     'description': token,
                     'assumption': transform(token) if '=' in token else ''})

        r"""filename = ''
        lineno = 0
        colno = 0
        threadid = 0
        desc = ''
        for traceLine in corralOutput.splitlines(True):
            traceMatch = traceP.match(traceLine)
            if traceMatch:
                filename = str(traceMatch.group(1))
                lineno = int(traceMatch.group(2))
                colno = int(traceMatch.group(3))
                threadid = int(traceMatch.group(4))
                desc = str(traceMatch.group(6))
                for e in desc.split(','):
                    e = e.strip()
                    assm = re.sub(
                        r'=(\s*\d+)bv\d+',
                        r'=\1',
                        e) if '=' in e else ''
                    trace = {'threadid': threadid,
                             'file': filename,
                             'line': lineno,
                             'column': colno,
                             'description': e,
                             'assumption': assm}
                    traces.append(trace)
            else:
                errorMatch = errorP.match(traceLine)
                if errorMatch:
                    filename = str(errorMatch.group(1))
                    lineno = int(errorMatch.group(2))
                    colno = int(errorMatch.group(3))
                    desc = str(errorMatch.group(4))"""
        errorMatch = errorP.search(corralOutput)
        assert errorMatch, 'Failed to obtain assertion failure info!'
        filename = str(errorMatch.group(1))
        lineno = int(errorMatch.group(2))
        colno = int(errorMatch.group(3))

        failsAt = {
            'file': filename,
            'line': lineno,
            'column': colno,
            'description': result.description()}

        json_data = {
            'verifier': 'corral',
            'passed?': False,
            'failsAt': failsAt,
            'threadCount': 1,
            'traces': traces
        }
    json_string = json.dumps(json_data)
    return json_string
