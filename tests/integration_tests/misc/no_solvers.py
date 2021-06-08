import os
import subprocess
import sys

python=sys.executable

def call_fuzzer(fn):
    cmd = './bin/yinyang "" ' + fn 
    output = subprocess.getoutput(cmd)
    return output

fn="examples/phi1.smt2"
out = call_fuzzer(fn)
if "Error: no solver specified" in out: 
    exit(0)
exit(1)

