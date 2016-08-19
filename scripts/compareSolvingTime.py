#!/usr/bin/env python3
import sys
for line in sys.stdin:
    sl = line.split()
    if len(sl) <= 1 or sl[1] != "OK":
        continue
    if len(sl) == 11:
        print(sl[4], sl[10])
    else:
        print(sl[4], sl[9])
