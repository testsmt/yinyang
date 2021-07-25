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

import os
import subprocess
import sys

python = sys.executable


def call_fuzzer(first_config, second_config, fn, opts):
    cmd = (
        python
        + " bin/opfuzz "
        + '"'
        + first_config
        + ";"
        + second_config
        + '" '
        + opts
        + " "
        + fn
    )
    output = subprocess.getoutput(cmd)
    print("$", cmd)
    print(output)
    crash_issues = 0
    for line in output.split("\n"):
        if "Detected crash bug:" in line:
            crash_issues += 1
    return crash_issues, cmd


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


def test_crash_list(msg, fn):
    print("Test", fn)
    solver = "crash.py"
    create_mocksolver_msg(msg, solver)
    first_config = os.path.abspath(solver)
    second_config = os.path.abspath(solver)
    opts = "-i 1 -m 1"
    crash, cmd = call_fuzzer(first_config, second_config, FN, opts)

    if crash != 1:
        print("[ERROR] Crash", fn, "cannot be captured.")
        print(cmd)
        exit(1)
    else:
        os.system("rm -rf " + solver)


if __name__ == "__main__":
    FN = "mock.smt2"
    create_mocksmt2(FN)
    root_folder = os.path.dirname(os.path.realpath(__file__))
    crash_folder = root_folder + "/crashes"
    for fn in os.listdir(crash_folder):
        fn = crash_folder + "/" + fn
        msg = open(fn).read()
        test_crash_list(msg, fn)
