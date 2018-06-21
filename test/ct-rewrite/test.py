#! /usr/bin/env python3
import os
import sys
d = os.path.dirname(os.path.realpath(__file__))

for fname in os.listdir(d + '/pass'):
    test = d + "/pass/" + fname
    res = test + ".out.wat"
    cmd = sys.argv[1] + " " + test + " -o " + res
    out = os.system(cmd)
    if (out != 0):
        print(fname + " Failed when it shouldn't")
        with open(out) as file:
            print(file.read())
            print("")
