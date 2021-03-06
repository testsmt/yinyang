import os,subprocess
import sys
N=2
python=sys.executable

def call_fuzzer(first_config, fn, opts):
    cmd = python+' yinyang.py '+ '"'+ first_config+ '" ' + opts + ' ' + fn
    # print(cmd)
    output = subprocess.getoutput(cmd)
    soundness_issues=None
    crash_issues = None
    for line in output.split("\n"):
        if "Soundness" in line:
            soundness_issues = int(line.split()[-1])
        if "Crash" in line:
            crash_issues = int(line.split()[-1])
        if "Ignored" in line:
            ignored_issues = int(line.split()[-1])

    return soundness_issues, crash_issues, ignored_issues, cmd

def get_z3():
    z3_link = "https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/z3-4.8.6-x64-ubuntu-16.04.zip"
    subprocess.getoutput("wget "+z3_link)
    subprocess.getoutput("unzip z3-4.8.6-x64-ubuntu-16.04.zip")
    return os.path.abspath("z3-4.8.6-x64-ubuntu-16.04/bin/z3")

def cleanup():
    subprocess.getoutput("rm -rf z3*")

cleanup()
#
# 1. download z3 and cvc4
#
print("Downloading solvers...")
print("Get z3")
z3 = get_z3()

# 2. ensure no soundness bugs in Semantic Fusion.
#
first_config=z3
fn='tests/integration_tests/semanticfusion/intersection-example-simple.proof-node75884.smt2 tests/integration_tests/semanticfusion/water_tank-node5020.smt2'
opts='-o unsat -s fusion'

print("Trying to sanitize unsat fusion...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, ignored_issues, cmd = call_fuzzer(first_config, fn, opts)
    if soundness_issues != 0 or crash_issues != 0 or ignored_issues != 0:
        bug_catched = True
        break

if bug_catched:
    print("[ERROR] Unexpected bugs found.")
    print(cmd)
    exit(1)

first_config=z3
fn='tests/integration_tests/semanticfusion/37315_issue-1694.smt2 tests/integration_tests/semanticfusion/37315_issue-1694.smt2'
opts='-o sat -s fusion'

print("Trying to sanitize sat fusion...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, ignored_issues, cmd = call_fuzzer(first_config, fn, opts)
    if soundness_issues != 0 or crash_issues != 0 or ignored_issues != 0:
        bug_catched = True
        break

if bug_catched:
    print("[ERROR] Unexpected bugs found.")
    print(cmd)
    exit(1)

cleanup()

print("[SUCCESS] All sanitizer passed .")
