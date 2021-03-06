import os
import subprocess
import sys

python=sys.executable

def call_fuzzer(first_config, second_config, fn, opts):
    cmd = python+' yinyang.py '+ '"'+ first_config+ ";" + second_config + '" ' + opts + ' ' + fn
    output = subprocess.getoutput(cmd)
    print(output)
    generated_seeds = None
    used_seeds = None
    crash_issues = None
    soundness_issues=None
    duplicate_issues=None
    timeout_issues=None
    ignored_issues=None
    for line in output.split("\n"):
        if "Generated mutants" in line:
            generated_seeds = int(line.split()[-1])
        if "Used seeds" in line:
            used_seeds = int(line.split()[-1])
        if "Crash" in line:
            crash_issues = int(line.split()[-1])
        if "Soundness" in line:
            soundness_issues = int(line.split()[-1])
        if "Duplicate" in line:
            duplicate_issues = int(line.split()[-1])
        if "Timeout" in line:
            timeout_issues = int(line.split()[-1])
        if "Ignored" in line:
            ignored_issues = int(line.split()[-1])

    return generated_seeds,used_seeds,crash_issues, soundness_issues, duplicate_issues, timeout_issues, ignored_issues, cmd

def create_mocksolver_msg(msg,script_fn):
    code= "#! /usr/bin/env python3\n"
    code+='msg="""'+msg+'"""\n'
    code+='print(msg)'
    open(script_fn,"w").write(code)
    os.system("chmod +x "+script_fn)

solver = "solver.py"
msg="sat"
create_mocksolver_msg(msg,solver)
first_config=os.path.abspath(solver)
second_config=os.path.abspath(solver)
opts='-i 1 -m 1'
FN=os.path.dirname(os.path.realpath(__file__))+"/too_large.smt2"
generated, used, crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,opts)
assert(generated == crash == soundness == duplicate == timeout == 0)
assert(used == ignored == 1)

