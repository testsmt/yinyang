import os,subprocess
import sys
N=300
python=sys.executable

def call_fuzzer(first_config, second_config, fn, opts):
    cmd = python+' yinyang.py '+ '"'+ first_config+ ";" + second_config + '" ' + opts + ' ' + fn
    print(cmd)
    output = subprocess.getoutput(cmd)
    soundness_issues=None
    crash_issues = None
    for line in output.split("\n"):
        if "Soundness" in line:
            soundness_issues = int(line.split()[-1])
        if "Crash" in line:
            crash_issues = int(line.split()[-1])

    return soundness_issues, crash_issues, cmd

def get_cvc4():
    cvc4_link = "https://github.com/CVC4/CVC4/releases/download/1.7/cvc4-1.7-x86_64-linux-opt"
    subprocess.getoutput("wget "+cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.7-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.7-x86_64-linux-opt")

def get_z3():
    z3_link = "https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/z3-4.8.6-x64-ubuntu-16.04.zip"
    subprocess.getoutput("wget "+z3_link)
    subprocess.getoutput("unzip z3-4.8.6-x64-ubuntu-16.04.zip")
    return os.path.abspath("z3-4.8.6-x64-ubuntu-16.04/bin/z3")

def cleanup():
    subprocess.getoutput("rm -rf cvc4*")
    subprocess.getoutput("rm -rf z3*")

cleanup()
#
# 1. download z3 and cvc4
#
print("Downloading solvers...")
print("Get cvc4")
cvc4 = get_cvc4()

print("Get z3")
z3 = get_z3()

# 2. check whether bugs can be retriggered
#
first_config=cvc4 + ' -q'
second_config=cvc4 + ' --sygus-inference -q'
fn='tests/integration_tests/opfuzz/cvc4_wrong_3564_hidden.smt2'
opts='-i 1 -m 1'

print("Trying to retrigger soundness bug...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(first_config, second_config, fn, opts)
    if soundness_issues == 1:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Soundness bug could not be reproduced.")
    print(cmd)
    exit(1)

first_config=z3+ ' model_validate=true'
second_config=cvc4+ ' --incremental --produce-models -q'
fn='tests/integration_tests/opfuzz/z3_invmodel_3118_hidden.smt2'
opts='-i 1 -m 1'

print("Trying to retrigger invalid model bug...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(first_config, second_config, fn, opts)
    if crash_issues != 0:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Invalid model bug could not be reproduced.")
    print(cmd)
    exit(1)

first_config=z3+ ' model_validate=true'
second_config=cvc4+ ' --incremental --produce-models -q'
fn='tests/integration_tests/opfuzz/z3-segfault-3549.smt2'
opts='-i 1 -m 1'

print("Trying to retrigger segfault...")
bug_catched = False
for _ in range(N):
    soundness_issues, crash_issues, cmd = call_fuzzer(first_config, second_config, fn, opts)
    if crash_issues != 0:
        bug_catched = True
        break

if not bug_catched:
    print("[ERROR] Crash bug could not be reproduced.")
    print(cmd)
    exit(1)

cleanup()

print("[SUCCESS] All bugs retriggered.")
