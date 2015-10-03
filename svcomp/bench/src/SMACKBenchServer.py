#!/usr/bin/python

import time
import argparse
import os
import subprocess

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

def unlock(lock_dir):
    try:
        os.rmdir(lock_dir)
    except:
        pass

def dequeue(filename, lock_folder):
    try:
        cur = None
        lock(lock_folder)
        with open(filename,'r+') as f:
            lines = f.readlines()
            f.seek(0)
            if len(lines)==0:
                unlock(lock_folder)
                return cur
            cur = lines[0].strip()
            lines = lines[1:]
            for line in lines:
                f.write(line)
            f.truncate()
    finally:
        unlock(lock_folder)
    return cur

def enqueue(data, filename, lock_folder):
    try:
        lock(lock_folder)
        with open(filename,'a') as f:
            f.write(data + '\n')
    finally:
        unlock(lock_folder)

def run_server():
    args = get_args()
    lock_folder = 'lck'
    while(True):
        cur = dequeue(args.queue_file, lock_folder)
        if cur:
            cur = cur.split()
            cmd =  ['./runSMACKBench.sh', cur[0], cur[1]]
            cmd += [args.thread_count, args.memory_limit]
            print(cmd)
            #cmd = ['ls']
            p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            while p.poll() is None:
                print(p.stdout.readline())
            print(p.stdout.read())
        else:
            time.sleep(10)
            

run_server()
#fcntl.lockf()
