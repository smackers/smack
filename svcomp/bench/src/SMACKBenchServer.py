#!/usr/bin/python

import fcntl
import time
import argparse
import os

def get_args():
    parser = argparse.ArgumentParser(description='Executes a SMACKBench jobs queue')
    parser.add_argument('--queue-file', required=True,
                        help='The file containing the list of jobs to process')
    parser.add_argument('--thread-count', required=True,
                        help='The number of concurrent benchmarks to run')
    parser.add_argument('--memory-limit', required=True,
                        help='The amount of memory to allocate to each concurrent run (in MB)')
    return parser.parse_args()

def lock(lock_dir):
    while True:
        try:
            os.mkdir(lock_dir)
            return
        except OSError as e:
            if e.errno != 17:
                raise
            print("here")
            time.sleep(1)

def unlock(lock_dir):
    try:
        os.rmdir(lock_dir)
    except:
        pass

def run_server():
    args = get_args()
    lock_folder = 'lck'
    while(True):
        try:
            lock(lock_folder)
            with open(args.queue_file,'r+') as f:
                lines = f.readlines()
                f.seek(0)
                cur = lines[0]
                if cur == "":
                    break
                lines = lines[1:]
                for line in lines:
                    f.write(line)
                print(cur.strip())
            unlock(lock_folder)
        except KeyboardInterrupt:
            unlock(lock_folder)
            exit()

            

run_server()
#fcntl.lockf()
