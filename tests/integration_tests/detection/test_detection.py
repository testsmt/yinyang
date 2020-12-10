"""
Script to test bug detection logic of Yin-Yang (src/modules/Fuzzer.py).
"""
import os,subprocess
import sys
import random

python=sys.executable
script_dir = os.path.dirname(os.path.realpath(__file__))
ERRORS=False

def is_sound(res1, res2):
    for i in range(len(res1)):
        if not (res1[i] == res2[i] or res1[i] == "unknown" or res2[i] == "unknown"): return False
    return True

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
    open(fn,"w").write("")

def create_mocksolver_msg(msg,script_fn):
    code= "#! /usr/bin/env python3\n"
    code+='msg="""'+msg+'"""\n'
    code+='print(msg)'
    open(script_fn,"w").write(code)
    os.system("chmod +x "+script_fn)

def create_mocksolver_segfault(script_fn):
    code= "#! /usr/bin/env python3\n"
    code+="import sys;sys.setrecursionlimit(1<<30);f=lambda f:f(f);f(f)"
    open(script_fn,"w").write(code)
    os.system("chmod +x "+script_fn)

def create_mocksolver_timeout(script_fn):
    code= "#! /usr/bin/env python3\n"
    code+="import time; time.sleep(30)"
    open(script_fn,"w").write(code)
    os.system("chmod +x "+script_fn)

def test_crash_list():
    print("1. Test crash list")
    solver = "crash.py"
    msg= """
    Fatal failure within void CVC4::SmtEngine::checkUnsatCore() at src/smt/smt_engine.cpp:1464
    Internal error detectedSmtEngine::checkUnsatCore(): produced core was satisfiable.
    Aborted
    """
    create_mocksolver_msg(msg,solver)
    first_config=os.path.abspath(solver)
    second_config=os.path.abspath(solver)
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,OPTS)

    if crash != 1:
        print("[ERROR] Crash cannot be captured.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+solver)

def test_ignore_list():
    print("2. Test ignore list")
    solver = "ignore_list.py"
    msg= """
    formula3.smt2:2.12: No set-logic command was given before this point.
    formula3.smt2:2.12: CVC4 will make all theories available.
    formula3.smt2:2.12: Consider setting a stricter logic for (likely) better performance.
    formula3.smt2:2.12: To suppress this warning in the future use (set-logic ALL).
    (error "Parse Error: formula3.smt2:2.23: Symbol 'Bdool' not declared as a type

      (declare-fun v () Bdool )
    ")
    """
    create_mocksolver_msg(msg,solver)
    first_config=os.path.abspath(solver)
    second_config=os.path.abspath(solver)
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,OPTS)

    if ignored != 2:
        print("[ERROR] Ignore list incorrect.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+solver)

def test_segfault():
    print("3. Test segfault")
    solver = "segfault.py"
    create_mocksolver_segfault(solver)
    first_config=os.path.abspath(solver)
    second_config=os.path.abspath(solver)
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,OPTS)

    if crash != 1:
        print("[ERROR] Segfault undetected.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+solver)

def test_timeout():
    print("4. Test timeout")
    timeout_solver = "timeout.py"
    sat_solver = "sat_solver.py"
    create_mocksolver_timeout(timeout_solver)
    msg="sat"
    create_mocksolver_msg(msg,sat_solver)
    opts=" -t 2 -i 1 -m 1"
    first_config=os.path.abspath(timeout_solver)
    second_config=os.path.abspath(sat_solver)
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,OPTS)

    if timeout != 1:
        print("[ERROR] Timeout undetected.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+timeout_solver)
        os.system("rm -rf "+sat_solver)


def test_empty_output():
    print("5. Test empty output")
    empty_solver = "empty_solver.py"
    sat_solver = "sat_solver.py"
    msg=""
    create_mocksolver_msg(msg,empty_solver)
    msg="sat"
    create_mocksolver_msg(msg,sat_solver)
    first_config=os.path.abspath(empty_solver)
    second_config=os.path.abspath(sat_solver)
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,OPTS)

    if ignored != 1:
        print("[ERROR] Empty output undetected.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+sat_solver)
        os.system("rm -rf "+empty_solver)

def test_unsoundness():
    print("6. Unsoundness")
    values = ["sat", "unsat", "unknown"]
    k = random.randint(1,20)
    res1 = random.choices(values, k=k)
    j = random.randint(0, k-1)
    res1[j] = random.choice(["sat", "unsat"])
    res2 = random.choices(values, k=k)
    while is_sound(res1,res2):
        res2 = random.choices(values, k=k)
    solver1="solver1.py"
    create_mocksolver_msg("\n".join(res1),solver1)
    solver2="solver2.py"
    first_config=os.path.abspath(solver1)
    second_config=os.path.abspath(solver2)
    create_mocksolver_msg("\n".join(res2),solver2)
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,OPTS)

    if soundness != 1:
        print("[ERROR] Unsundness undetected.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+solver1)
        os.system("rm -rf "+solver2)

def test_soundness():
    print("7. Soundness")
    values = ["sat", "unsat", "unknown"]
    k = random.randint(1,20)
    res1 = random.choices(values, k=k)
    res2 = res1
    j = random.randint(0, k-1)
    res1[j] = random.choice(["sat", "unsat"])

    for i in range(len(res1)):
        if (res1[i] == "sat" or res1[i] == "unsat") and random.choice([True, False]):
            res2[i] = "unknown"
    solver1="solver1.py"
    create_mocksolver_msg("\n".join(res1),solver1)
    solver2="solver2.py"
    first_config=os.path.abspath(solver1)
    second_config=os.path.abspath(solver2)
    create_mocksolver_msg("\n".join(res2),solver2)
    crash, soundness, duplicate, timeout, ignored, cmd = call_fuzzer(first_config, second_config, FN,OPTS)

    if soundness != 0:
        print("[ERROR] False positive.")
        print(cmd)
        ERRORS=True
    else:
        os.system("rm -rf "+solver1)
        os.system("rm -rf "+solver2)

if __name__ == "__main__":
    # Create empty mock.smt2, set fuzzer opts
    FN= "mock.smt2"
    create_mocksmt2(FN)
    OPTS='-i 1 -m 1'
    test_crash_list()
    test_ignore_list()
    test_segfault()
    test_timeout()
    test_empty_output()
    test_unsoundness()
    test_soundness()
    if not ERRORS:
        print("[SUCCESS] All tests passed.")

