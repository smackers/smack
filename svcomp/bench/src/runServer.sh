#!/bin/bash

. /mnt/local/smack-project/smack.environment
host=$(hostname)
nohup ./SMACKBenchServer.py --queue-file queue --thread-count 8 --memory-limit 15000 >>${host}.out 2>&1&
