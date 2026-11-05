# MIT License
#
# Copyright (c) [2020 - 2021] The yinyang authors
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""
Script to test bug detection logic of yinyang (src/core/Fuzzer.py).
"""
import os
import sys
import random
import shutil
import subprocess
import tempfile

python = sys.executable
script_dir = os.path.dirname(os.path.realpath(__file__))
ERRORS = False


def newest_log(path):
    files = os.listdir(path)
    paths = [os.path.join(path, basename) for basename in files]
    return max(paths, key=os.path.getctime)


def is_sound(res1, res2):
    for i in range(len(res1)):
        if not (res1[i] == res2[i] or res1[i] == "unknown" 
                or res2[i] == "unknown"):
            return False
    return True


def run_fuzzer(first_config, second_config, fn, opts):
    cmd = (
        python
        + " bin/opfuzz "
        + opts
        + '"'
        + first_config
        + ";"
        + second_config
        + '" '
        + " "
        + fn
    )
    status, output = subprocess.getstatusoutput(cmd)
    print("$", cmd)
    print(output, flush=True)
    return status, output, cmd


def call_fuzzer(first_config, second_config, fn, opts):
    status, output, cmd = run_fuzzer(first_config, second_config, fn, opts)
    crash_issues = 0
    soundness_issues = 0
    segfault_issues = 0
    duplicate_issues = 0
    timeout_issues = None
    ignored_issues = None
    for line in output.split("\n"):
        if "Detected crash bug" in line:
            crash_issues += 1
        if "Detected soundness bug" in line:
            soundness_issues += 1
        if "Detected segfault" in line:
            segfault_issues += 1
        if "Duplicate. Stop testing on this seed." in line:
            duplicate_issues += 1
        if "Ignored" in line:
            ignored_issues = int(line.split()[-1])

    return (
        crash_issues,
        soundness_issues,
        segfault_issues,
        duplicate_issues,
        timeout_issues,
        ignored_issues,
        cmd,
    )


def create_mocksmt2(fn):
    open(fn, "w").write(
        "(declare-fun x () Int)\n(declare-fun y () Int)\n(assert (= x y))"
    )


def create_mocksolver_msg(msg, script_fn):
    code = "#! /usr/bin/env python3\n"
    code += 'msg="""' + msg + '"""\n'
    code += "print(msg)"
    open(script_fn, "w").write(code)
    os.system("chmod +x " + script_fn)


def create_mocksolver_segfault(script_fn):
    # Deliberately unbounded recursion used to rely on blowing the C stack
    # to raise a genuine SIGSEGV, but CPython 3.11+ enforces a C stack
    # depth check that raises RecursionError before that happens, so the
    # process no longer actually segfaults. Send SIGSEGV directly instead,
    # which is deterministic and portable across Python versions.
    code = "#! /usr/bin/env python3\n"
    code += "import os, signal; os.kill(os.getpid(), signal.SIGSEGV)"
    open(script_fn, "w").write(code)
    os.system("chmod +x " + script_fn)


def create_mocksolver_signal(script_fn, signame, msg=""):
    # Mock solver that prints msg and then kills itself with signal signame.
    code = "#! /usr/bin/env python3\n"
    code += "import os, signal\n"
    code += "print(" + repr(msg) + ", flush=True)\n"
    code += "os.kill(os.getpid(), signal." + signame + ")"
    open(script_fn, "w").write(code)
    os.system("chmod +x " + script_fn)


def create_mocksolver_exitcode(script_fn, exitcode):
    # Mock solver that exits like a shell wrapper whose child got a signal.
    code = "#! /usr/bin/env python3\n"
    code += "import sys; sys.exit(" + str(exitcode) + ")"
    open(script_fn, "w").write(code)
    os.system("chmod +x " + script_fn)


def create_mocksolver_timeout(script_fn):
    code = "#! /usr/bin/env python3\n"
    code += "import time; time.sleep(30)"
    open(script_fn, "w").write(code)
    os.system("chmod +x " + script_fn)


def test_crash_list():
    print("*** (1) Test crash list")
    solver = "crash.py"
    msg = """
    Fatal failure within void CVC4::SmtEngine::checkUnsatCore() at src/smt/smt_engine.cpp:1464
    Internal error detectedSmtEngine::checkUnsatCore(): produced core was satisfiable.
    Aborted
    """  # noqa: E501
    create_mocksolver_msg(msg, solver)
    first_config = os.path.abspath(solver)
    second_config = os.path.abspath(solver)
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )

    if crash != 1:
        print("[ERROR] Crash cannot be captured.")
        print(cmd)
        exit(1)
    else:
        os.system("rm -rf " + solver)


def test_ignore_list():
    print("*** (2) Test ignore list")
    solver = "ignore_list.py"
    msg = """
    formula3.smt2:2.12: No set-logic command was given before this point.
    formula3.smt2:2.12: CVC4 will make all theories available.
    formula3.smt2:2.12: Consider setting a stricter logic for (likely) better performance.
    formula3.smt2:2.12: To suppress this warning in the future use (set-logic ALL).
    (error "Parse Error: formula3.smt2:2.23: Symbol 'Bdool' not declared as a type

      (declare-fun v () Bdool )
    ")
    """  # noqa: E501

    create_mocksolver_msg(msg, solver)
    first_config = os.path.abspath(solver)
    second_config = os.path.abspath(solver)
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )

    log = open(newest_log("logs")).read()
    if log.count("Invalid mutant:ignore_list") != 2:
        print("[ERROR] Ignore list incorrect.")
        print(cmd)
        exit(1)
    else:
        os.system("rm -rf " + solver)


def test_segfault():
    print("*** (3) Test segfault")
    solver = "segfault.py"
    create_mocksolver_segfault(solver)
    first_config = os.path.abspath(solver)
    second_config = os.path.abspath(solver)
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )

    if segfault != 1:
        print("[ERROR] Segfault undetected.")
        print(cmd)
        exit(1)

    # The fuzzer must also survive the segfault and finish the run normally.
    status, output, cmd = run_fuzzer(first_config, second_config, FN, OPTS)
    if status != 10 or "All seeds processed" not in output:
        print("[ERROR] Fuzzer did not finish normally after a segfault.")
        print(cmd)
        exit(1)
    os.system("rm -rf " + solver)


def test_crash_signals():
    print("*** (8) Test crash signals")
    solver = "signal_solver.py"
    cases = [
        ("SIGABRT", ""),
        ("SIGFPE", ""),
        ("SIGBUS", ""),
        ("SIGILL", ""),
        # A crash must not be hidden by the ignore list.
        ("SIGABRT", '(error "unsupported")'),
    ]
    for signame, msg in cases:
        create_mocksolver_signal(solver, signame, msg)
        first_config = os.path.abspath(solver)
        status, output, cmd = run_fuzzer(first_config, first_config, FN, OPTS)
        if (output.count("Detected crash bug (" + signame + ")") != 1
                or status != 10):
            print("[ERROR] Crash by " + signame + " undetected.")
            print(cmd)
            exit(1)

    # Exit code 128 + N, as reported by a shell wrapper.
    for exitcode in [134, 139]:
        create_mocksolver_exitcode(solver, exitcode)
        first_config = os.path.abspath(solver)
        status, output, cmd = run_fuzzer(first_config, first_config, FN, OPTS)
        if status != 10:
            print("[ERROR] Exit code " + str(exitcode) + " undetected.")
            print(cmd)
            exit(1)

    # Signals sent from outside the solver are not crashes.
    create_mocksolver_signal(solver, "SIGTERM")
    first_config = os.path.abspath(solver)
    status, output, cmd = run_fuzzer(first_config, first_config, FN, OPTS)
    if status != 0 or "Detected crash bug" in output:
        print("[ERROR] SIGTERM reported as a crash.")
        print(cmd)
        exit(1)
    os.system("rm -rf " + solver)


def test_timeout():
    print("*** (4) Test timeout")
    timeout_solver = "timeout.py"
    sat_solver = "sat_solver.py"
    create_mocksolver_timeout(timeout_solver)
    msg = "sat"
    create_mocksolver_msg(msg, sat_solver)
    first_config = os.path.abspath(timeout_solver)
    second_config = os.path.abspath(sat_solver)
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )
    log = open(newest_log("logs")).read()

    if log.count("Solver timeout occurred.") != 1:
        print("[ERROR] Timeout undetected.")
        print(cmd)
        exit(1)
    else:
        os.system("rm -rf " + timeout_solver)
        os.system("rm -rf " + sat_solver)


def test_empty_output():
    print("*** (5) Test empty output")
    empty_solver = "empty_solver.py"
    sat_solver = "sat_solver.py"
    msg = ""
    create_mocksolver_msg(msg, empty_solver)
    msg = "sat"
    create_mocksolver_msg(msg, sat_solver)
    first_config = os.path.abspath(empty_solver)
    second_config = os.path.abspath(sat_solver)
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )
    log = open(newest_log("logs")).read()
    if log.count("Invalid mutant") != 1:
        print("[ERROR] Empty output undetected.")
        print(cmd)
        exit(1)
    else:
        os.system("rm -rf " + sat_solver)
        os.system("rm -rf " + empty_solver)


def test_unsoundness():
    print("*** (6) Unsoundness")
    values = ["sat", "unsat", "unknown"]
    k = random.randint(1, 20)
    res1 = random.choices(values, k=k)
    j = random.randint(0, k - 1)
    res1[j] = random.choice(["sat", "unsat"])
    res2 = random.choices(values, k=k)
    while is_sound(res1, res2):
        res2 = random.choices(values, k=k)
    solver1 = "solver1.py"
    create_mocksolver_msg("\n".join(res1), solver1)
    solver2 = "solver2.py"
    first_config = os.path.abspath(solver1)
    second_config = os.path.abspath(solver2)
    create_mocksolver_msg("\n".join(res2), solver2)
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )

    if soundness != 1:
        print("[ERROR] Unsoundness undetected.")
        print(cmd)
        exit(1)
    else:
        os.system("rm -rf " + solver1)
        os.system("rm -rf " + solver2)


def test_soundness():
    print("*** (7) Soundness")
    values = ["sat", "unsat", "unknown"]
    k = random.randint(1, 20)
    res1 = random.choices(values, k=k)
    res2 = res1
    j = random.randint(0, k - 1)
    res1[j] = random.choice(["sat", "unsat"])

    for i in range(len(res1)):
        if (res1[i] == "sat" or res1[i] == "unsat")\
           and random.choice([True, False]):
            res2[i] = "unknown"
    solver1 = "solver1.py"
    create_mocksolver_msg("\n".join(res1), solver1)
    solver2 = "solver2.py"
    first_config = os.path.abspath(solver1)
    second_config = os.path.abspath(solver2)
    create_mocksolver_msg("\n".join(res2), solver2)
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )

    if soundness != 0:
        print("[ERROR] False positive.")
        print(cmd)
        exit(1)
    else:
        os.system("rm -rf " + solver1)
        os.system("rm -rf " + solver2)


def test_duplicate_list():
    print("*** (9) Test duplicate list")
    solver = "crash.py"
    # The crash location is not in the default duplicate_list, so the crash
    # is only a duplicate if the user's .yinyang/Config.py is loaded.
    msg = """
Fatal failure within void CVC4::SmtEngine::checkUnsatCore() at src/smt/smt_custom.cpp:42
Internal error detectedSmtEngine::checkMock(): produced core was satisfiable.
Aborted
"""  # noqa: E501
    config_py = """
duplicate_list = [
    "src/smt/smt_custom.cpp:42"
]
"""
    create_mocksolver_msg(msg, solver)
    first_config = os.path.abspath(solver)
    second_config = os.path.abspath(solver)

    # Without a user config the crash is reported as a new bug.
    crash, soundness, segfault, duplicate, timeout, ignored, cmd = call_fuzzer(
        first_config, second_config, FN, OPTS
    )
    if crash != 1 or duplicate != 0:
        print("[ERROR] Crash with default config cannot be captured.")
        print(cmd)
        exit(1)

    if os.path.exists(".yinyang"):
        os.rename(".yinyang", ".yinyang.orig")
    os.mkdir(".yinyang")
    with open(".yinyang/Config.py", "w") as f:
        f.write(config_py)
    try:
        crash, soundness, segfault, duplicate, timeout, ignored, cmd = \
            call_fuzzer(first_config, second_config, FN, OPTS)
        log = open(newest_log("logs")).read()
    finally:
        os.system("rm -rf .yinyang")
        if os.path.exists(".yinyang.orig"):
            os.rename(".yinyang.orig", ".yinyang")
    if log.count("Duplicate.") != 1 or crash != 0:
        print("[ERROR] Duplicate crash cannot be captured.")
        print(cmd)
        exit(1)
    os.system("rm -rf " + solver)


def test_bug_files():
    print("*** (10) Bug trigger and its .output share one name")
    segfault = os.path.abspath("segfault.py")
    create_mocksolver_segfault(segfault)
    sat = os.path.abspath("sat.py")
    create_mocksolver_msg("sat", sat)
    unsat = os.path.abspath("unsat.py")
    create_mocksolver_msg("unsat", unsat)
    # report() for crashes, report_diff() for soundness bugs
    for first_config, second_config in [(segfault, segfault), (sat, unsat)]:
        bugs = tempfile.mkdtemp()
        status, output, cmd = run_fuzzer(
            first_config, second_config, FN, OPTS + "-b " + bugs + " "
        )
        files = os.listdir(bugs)
        stems = set(os.path.splitext(fn)[0] for fn in files)
        if len(files) != 2 or len(stems) != 1:
            print("[ERROR] Expected one .smt2 and one .output with the same"
                  " name, got: " + str(sorted(files)))
            print(cmd)
            exit(1)
        shutil.rmtree(bugs)
    for solver in [segfault, sat, unsat]:
        os.remove(solver)


if __name__ == "__main__":
    # Create empty mock.smt2, set fuzzer opts
    FN = "mock.smt2"
    create_mocksmt2(FN)
    OPTS = "-i 1 -m 1 "
    test_crash_list()
    print()
    test_ignore_list()
    print()
    test_segfault()
    print()
    test_timeout()
    print()
    test_empty_output()
    print()
    test_unsoundness()
    print()
    test_soundness()
    print()
    test_crash_signals()
    print()
    test_duplicate_list()
    print()
    test_bug_files()
