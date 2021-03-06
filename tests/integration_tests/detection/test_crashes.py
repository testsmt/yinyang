import os
import subprocess
import sys

python=sys.executable

def call_fuzzer(first_config, second_config, fn, opts):
    cmd = python+' yinyang.py '+ '"'+ first_config+ ";" + second_config + '" ' + opts + ' ' + fn
    output = subprocess.getoutput(cmd)
    # print(output)
    crash_issues = None
    soundness_issues=None
    duplicate_issues=None
    timeout_issues=None
    ignored_issues=None
    for line in output.split("\n"):
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

    return crash_issues, soundness_issues, duplicate_issues, timeout_issues, ignored_issues, cmd

def create_mocksmt2(fn):
    open(fn,"w").write("(declare-fun x () Int)\n(declare-fun y () Int)\n(assert (= x y))")

def create_mocksolver_msg(msg,script_fn):
    code= "#! /usr/bin/env python3\n"
    code+='msg="""'+msg+'"""\n'
    code+='print(msg)'
    open(script_fn,"w").write(code)
    os.system("chmod +x "+script_fn)

def test_crash_list(msg,fn):
    print("Test", fn)
    solver = "crash.py"
    create_mocksolver_msg(msg,solver)
    first_config=os.path.abspath(solver)
    second_config=os.path.abspath(solver)
    opts='-i 1 -m 1'
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,opts)

    if crash != 1:
        print("[ERROR] Crash", fn, "cannot be captured.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+solver)

if __name__ == "__main__":
    FN="mock.smt2"
    create_mocksmt2(FN)
    root_folder=os.path.dirname(os.path.realpath(__file__))
    crash_folder = root_folder+"/crashes"
    for fn in os.listdir(crash_folder):
        fn=crash_folder+"/"+fn
        msg = open(fn).read()
        test_crash_list(msg,fn)
