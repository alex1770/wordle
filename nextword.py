#!/usr/bin/env python3

# Simple example next word generator that could be used with the wordle.cpp option -j prog:nextword.py
# This ignores the arguments passed to it, which is a list of the toplevel words previously evaluated

import os,fcntl

countfile="joblist_wordcount"
wordfile="joblist_wordlist"

fd=os.open(wordfile,os.O_RDWR)
fcntl.flock(fd,fcntl.LOCK_EX)
fpw=os.fdopen(fd,mode="r")

if os.path.isfile(countfile):
  with open(countfile) as fp: n=int(fp.read())
else:
  n=0

# Yes it's order n^2 to read through the file to get to the word, but it's negligible time
for i in range(n): dum=fpw.readline()
ret=fpw.readline()
if ret=="":
  print("xxxxx")
else:
  print(ret.strip())
  with open(countfile,"w") as fpc: print(n+1,file=fpc)

# File descriptors are closed and locks released on exit
