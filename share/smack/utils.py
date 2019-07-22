import os
import sys
import tempfile
import subprocess
import signal
from threading import Timer
import smack.top

temporary_files = []

def temporary_file(prefix, extension, args):
    handler, name = tempfile.mkstemp(extension, prefix + '-', os.getcwd(), True)
    os.close(handler)
    if not args.debug:
        temporary_files.append(name)
    return name

def remove_temp_files():
    for file_name in temporary_files:
        if os.path.isfile(file_name):
            os.unlink(file_name)

def timeout_killer(proc, timed_out):
    if not timed_out[0]:
        timed_out[0] = True
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

def try_command(cmd, cwd=None, console=False, timeout=None):
    args = smack.top.smack_args
    console = (console or args.verbose or args.debug) and not args.quiet
    filelog = args.debug
    output = ''
    proc = None
    timer = None
    try:
        if args.debug:
            print "Running %s" % " ".join(cmd)

        proc = subprocess.Popen(cmd, cwd=cwd, preexec_fn=os.setsid,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

        if timeout:
            timed_out = [False]
            timer = Timer(timeout, timeout_killer, [proc, timed_out])
            timer.start()

        if console:
            while True:
                line = proc.stdout.readline()
                if line:
                    output += line
                    print line,
                elif proc.poll() is not None:
                    break
            proc.wait
        else:
            output = proc.communicate()[0]

        if timeout:
            timer.cancel()

        ret_code = proc.returncode
        proc = None
        if timeout and timed_out[0]:
            return output + ("\n%s timed out." % cmd[0])
        elif ret_code == -signal.SIGSEGV:
            raise Exception("segmentation fault")
        elif ret_code and args.verifier != 'symbooglix':
            raise Exception(output)
        else:
            return output

    except (RuntimeError, OSError) as err:
        print >> sys.stderr, output
        sys.exit("Error invoking command:\n%s\n%s" % (" ".join(cmd), err))

    finally:
        if timeout and timer:
            timer.cancel()
        if proc:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        if filelog:
            with open(temporary_file(cmd[0], '.log', args), 'w') as log_file:
                log_file.write(output)
