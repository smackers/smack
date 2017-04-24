import os
import sys
import tempfile
import subprocess
import signal
from threading import Timer
import top

temporary_files = []

def temporary_file(prefix, extension, args):
  f, name = tempfile.mkstemp(extension, prefix + '-', os.getcwd(), True)
  os.close(f)
  if not args.debug:
    temporary_files.append(name)
  return name

def remove_temp_files():
  for f in temporary_files:
    if os.path.isfile(f):
      os.unlink(f)

def timeout_killer(proc, timed_out):
  if not timed_out[0]:
    timed_out[0] = True
    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

def try_command(cmd, cwd=None, console=False, timeout=None):
  args = top.args
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

    rc = proc.returncode
    proc = None
    if timeout and timed_out[0]:
      return output + ("\n%s timed out." % cmd[0])
    elif rc == -signal.SIGSEGV:
      raise Exception("segmentation fault")
    elif rc:
      raise Exception(output)
    else:
      return output

  except (RuntimeError, OSError) as err:
    print >> sys.stderr, output
    sys.exit("Error invoking command:\n%s\n%s" % (" ".join(cmd), err))

  finally:
    if timeout and timer: timer.cancel()
    if proc: os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    if filelog:
      with open(temporary_file(cmd[0], '.log', args), 'w') as f:
        f.write(output)
