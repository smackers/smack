#! /usr/bin/env python

from os import path
from multiprocessing.pool import ThreadPool
import multiprocessing
import os
import signal
import logging
import yaml
import argparse
from os import path
import subprocess
import re
import glob
import time
import sys

OVERRIDE_FIELDS = ['verifiers', 'memory', 'time-limit', 'skip']
APPEND_FIELDS = ['flags']

# integer constants
PASSED = 0
TIMEDOUT = 1
UNKNOWN = 2
FAILED = -1

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def get_result(output):
  if re.search(r'[1-9]\d* time out|Z3 ran out of resources|z3 timed out|Corral timed out', output):
    return 'timeout'
  elif re.search(r'[1-9]\d* verified, 0 errors?|no bugs', output):
    return 'verified'
  elif re.search(r'0 verified, [1-9]\d* errors?|can fail', output):
    return 'error'
  else:
    return 'unknown'

def merge(metadata, yamldata):

  for key in OVERRIDE_FIELDS:
    if key in yamldata:
      metadata[key] = yamldata[key]

  for key in APPEND_FIELDS:
    if key in yamldata:
      if key in metadata:
        metadata[key] += yamldata[key]
      else:
        metadata[key] = yamldata[key]

def metadata(file):
  m = {}
  prefix = []

  for d in path.dirname(file).split('/'):
    prefix += [d]
    yaml_file = path.join(*(prefix + ['config.yml']))
    if path.isfile(yaml_file):
      with open(yaml_file, "r") as f:
        data = yaml.safe_load(f)
        merge(m,data)

  with open(file, "r") as f:
    for line in f.readlines():

      match = re.search(r'@skip', line)
      if match:
        m['skip'] = True

      match = re.search(r'@flag (.*)',line)
      if match:
        m['flags'] += [match.group(1).strip()]

      match = re.search(r'@expect (.*)',line)
      if match:
        m['expect'] = match.group(1).strip()

  if not m['skip'] and not 'expect' in m:
    print red("WARNING: @expect MISSING IN %s" % file)
    m['expect'] = 'verified'

  return m
  
parser = argparse.ArgumentParser()
parser.add_argument("--exhaustive", help="be exhaustive", action="store_true")
args = parser.parse_args()

print "Running regression tests..."
print

passed = failed = timeouts = unknowns = 0

try:
  for test in glob.glob("./**/*.c"):
    meta = metadata(test)

    if meta['skip'] == True:
      continue

    if meta['skip'] != False and not args.exhaustive:
      return

    str_result = "{0:>20}\n".format(test)

    print "{0:>20}".format(test)
    sys.stdout.flush()

    cmd = ['smackverify.py', test]
    cmd += ['--time-limit', str(meta['time-limit'])]
    cmd += ['-o', path.splitext(test)[0] + '.bpl']
    cmd += meta['flags']

    for memory in meta['memory'][:100 if args.exhaustive else 1]:
      cmd += ['--mem-mod=' + memory]

      for verifier in meta['verifiers'][:100 if args.exhaustive else 1]:
        cmd += ['--verifier=' + verifier]

        print "{0:>20} {1:>10}    :".format(memory, verifier),

        try:
          t0 = time.time()
          p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
          out, err  = p.communicate()
          elapsed = time.time() - t0

        except OSError:
          print >> sys.stderr
          sys.exit("Error executing command:\n%s" % " ".join(cmd))

        result = get_result(out+err)

        if result == meta['expect']:
          print green('PASSED '),
          passed += 1

        elif result == 'timeout':
          print red('TIMEOUT'),
          timeouts += 1

        elif result == 'unknown':
          print red('UNKNOWN'),
          unknowns += 1

        else:
          print red('FAILED '),
          failed += 1

        print '  [%.2fs]' % round(elapsed, 2)
        sys.stdout.flush()
  
except KeyboardInterrupt:
  pass

print
print ' PASSED count:', passed
print ' FAILED count:', failed

        # returns a status code based on the results of the test
        if passed:
            return PASSED
        elif timedout:
            return TIMEDOUT
        elif unknown:
            return UNKNOWN
        else:
            return FAILED


def init_worker():
    """
    Set up the worker processes to ignore SIGINT altogether. This confines all
    the cleanup code to the parent process.

    Reference: http://stackoverflow.com/a/6191991/3342427
    """
    #signal.signal(signal.SIGINT, signal.SIG_IGN)

def main():
    """
    Main entry point for the test suite.
    """
    
    num_cpus = multiprocessing.cpu_count()

    # configure the CLI
    parser = argparse.ArgumentParser()
    parser.add_argument("--exhaustive", help="be exhaustive", action="store_true")
    parser.add_argument("--threads", action="store", dest="n_threads", default=num_cpus, type=int,
                        help="execute regressions using the selected number of threads in parallel")
    parser.add_argument("--log", action="store", dest="log_level", default="DEBUG", type=str,
                        help="sets the logging level (DEBUG, INFO, WARNING)")
    parser.add_argument("--output_log", action="store", dest="log_path", type=str,
                        help="sets the output log path. (std out by default)")
    args = parser.parse_args()


    # configure the logging
    log_format = ''
    log_level = logging.DEBUG

    # add more log levels later (if needed)
    if args.log_level.upper() == "INFO":
        log_level = logging.INFO
    elif args.log_level.upper() == "WARNING":
        log_level = logging.WARNING

    # if the user supplied a log path, write the logs to that file.
    # otherwise, write the logs to std out.
    if args.log_path:
        logging.basicConfig(filename=args.log_path, format=log_format, level=log_level)
    else:
        logging.basicConfig(format=log_format, level=log_level)

    logging.debug("Creating Pool with '%d' Workers" % args.n_threads)
    p = ThreadPool(processes=args.n_threads, initializer=init_worker)

    # start the tests
    logging.info("Running regression tests...")
    passed = failed = timeouts = unknowns = 0

    # start processing the tests. this blocks the main thread
    async_results = []
    for test in glob.glob("./**/*.c"):
        async_results.append(p.apply_async(process_test, args=(test, args,)))

    try:
        # keep the main thread active while there are active workers
        count = 0
        while True:
            if count == len(async_results):
                break;

            # iterate over the results from each worker
            for r in async_results:
                try:
                    # if the worker has completed its task, get the result
                    # from it.
                    if r.successful:
                        test_result = r.get()
                        if test_result == PASSED:
                            passed += 1
                        elif test_result == TIMEDOUT:
                            timeouts += 1
                        elif test_result == UNKNOWN:
                            unknowns += 1
                        elif test_result == FAILED:
                            failed += 1
                        count += 1
                except AssertionError:
                    continue

    except KeyboardInterrupt:
      logging.debug("Caught KeyboardInterrupt, terminating workers")
      p.terminate() # terminate any remaining workers
      p.join()
    else:
      logging.debug("Quitting normally")
      # close the pool. this prevents any more tasks from being submitted.
      p.close()
      p.join() # wait for all workers to finish their tasks

    # log the test results
    logging.info(' PASSED count: %d' % passed)
    logging.info(' FAILED count: %d' % failed)
    logging.info(' TIMEOUT count: %d' % timeouts)
    logging.info(' UNKNOWN count: %d' % unknowns)

if __name__=="__main__":
    main()
