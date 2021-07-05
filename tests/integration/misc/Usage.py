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
Integration test for usage part in README.md.
"""
import os
import sys
import subprocess

import_path = os.path.dirname(
    os.path.dirname(
        os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
)
sys.path.append(import_path)

python = sys.executable

TIME_LIMIT = 30


def run_opfuzz(first_config, second_config, directory, opts, timeout_limit):
    timeout = "timeout --signal=INT " + str(timeout_limit) + " "
    cmd = (
        timeout
        + python
        + " bin/opfuzz "
        + '"'
        + first_config
        + ";"
        + second_config
        + '" '
        + opts
        + " "
        + directory
    )
    print(cmd, flush=True)
    output = subprocess.getoutput(cmd)
    return output, cmd


def error(output):
    if "Traceback" in output:
        return True
    if "error" in output or "Error" in output:
        return True
    return False


def get_cvc4():
    cvc4_link = "https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt"  # noqa: E501
    subprocess.getoutput("wget " + cvc4_link)
    subprocess.getoutput("chmod +x cvc4-1.8-x86_64-linux-opt")
    return os.path.abspath("cvc4-1.8-x86_64-linux-opt")


def get_z3():
    z3_link = "https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip"  # noqa: E501
    subprocess.getoutput("wget " + z3_link)
    subprocess.getoutput("unzip z3-4.8.10-x64-ubuntu-18.04.zip")
    return os.path.abspath("z3-4.8.10-x64-ubuntu-18.04/bin/z3")


def cleanup():
    subprocess.getoutput("rm -rf cvc4*")
    subprocess.getoutput("rm -rf z3*")
    subprocess.getoutput("rm -rf QF_LIA")


def get_dir(benchmark):
    if "incremental" in benchmark:
        return benchmark.split(" ")[-1]
    else:
        return benchmark.split("/")[-1].split(".")[0]


# 1. Get SMT-LIB 2 benchmarks.
cleanup()

print("(1) Get SMT-LIB 2 benchmark", flush=True)
cmd = "git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIA.git"  # noqa: E501
print(cmd)
subprocess.getoutput(cmd)
print("-" * 100)

print("(2) Get and build SMT solvers.", flush=True)
z3 = get_z3()
cvc4 = get_cvc4()
print("-" * 100)

print("(3) Run Yin-Yang on the benchmarks e.g. with Z3 and CVC4.", flush=True)
first_config = z3 + " model_validate=true"
second_config = cvc4 + " --check-models -m -i -q"
output, cmd = run_opfuzz(first_config, second_config, "QF_LIA", "", TIME_LIMIT)
print(output, flush=True)
if error(output):
    print("An error occurred!")
    print("cmd=" + cmd)
    exit(1)
cleanup()
print("-" * 100)
