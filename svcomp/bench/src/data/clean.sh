#!/usr/local/bin/bash

#Deletes bpl and bc files that were last modified more than 2 hours ago
find . -name "*.bpl" -mmin +120 -delete
find . -name "*.bc" -mmin +120 -delete
find . -name "*.ll" -mmin +120 -delete
