#!/usr/bin/env python3
import sys
for line in sys.stdin:
    sl = line.split()
    if sl[1] != "OK":
        continue
    print(sl[4], sl[10])
