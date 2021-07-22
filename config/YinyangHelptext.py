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

from src.base.Version import VERSION, COMMIT


header = (
    "yinyang -- a differential fuzzer for SMT solvers [version: "
    + VERSION
    + " ("
    + COMMIT
    + ")]"
)

usage = """ yinyang [options] -o oracle solver_clis seed_file1 seed_file2 [optionally, more seed files]
       yinyang [options] -o oracle solver_clis seed_folder [optionally, more seed folders]

       solver_clis := "solver_cli1;solver_cli2;...;solver_clik"
       oracle      := {sat,unsat}
"""  # noqa: E501

short_description = """
yinyang is a tool for finding bugs in SMT solver by generating mutant SMT-LIB
scripts from a set of seed SMT-LIB scripts (.smt2 files) with known satisfiability
(i.e. either sat or unsat) and generates mutant formulas of the same satisfiability.
yinyang realizes semantic fusion and can work with a single SMT solver.

Example (basic usage):
$ yinyang -o sat "z3 model_validate=true" semantic-fusion-seeds/QF_NRA/sat
[2021/06/18 11:25:14 AM] Strategy: yinyang, 1 testing targets, 19228225 seeds
[2021/06/18 11:25:14 AM] Performed 0 solver calls (0.0 calls/s, eff: NaN, 0.0 mutants/s)
[2021/06/18 11:25:22 AM] Performed 2 solver calls (0.2 calls/s, eff: 50.0%, 0.1 mutants/s)
[2021/06/18 11:25:30 AM] Performed 4 solver calls (0.2 calls/s, eff: 50.0%, 0.1 mutants/s)
[2021/06/18 11:25:38 AM] Performed 6 solver calls (0.2 calls/s, eff: 50.0%, 0.1 mutants/s)
[2021/06/18 11:25:47 AM] Performed 12 solver calls (0.4 calls/s, eff: 66.7%, 0.2 mutants/s)
[2021/06/18 11:25:55 AM] Performed 14 solver calls (0.3 calls/s, eff: 64.3%, 0.2 mutants/s)
User interrupt
16 seeds processed, 16 valid, 0 invalid
0 bug triggers found

This will by default randomly select smt2 files from `./semantic-fusion-seeds/QF_NRA/sat`
and generate 30 mutants per file. If a bug has been found, yinyang will store it
in `./bugs`. You can use the shortcut CTRL+C to terminate yinyang manually.
You can obtain pre-categorized seeds from the following GitHub repository:

    https://github.com/testsmt/semantic-fusion-seeds

For a listing of options and further information, use yinyang --help."""  # noqa: E501


long_description = """
yinyang is a tool for finding bugs in SMT solver by generating mutant SMT-LIB
scripts from a set of seed SMT-LIB scripts (.smt2 files) with known
satisfiability (i.e. either sat or unsat) and generates mutant formulas of the
same satisfiability. yinyang realizes semantic fusion which can work with a
single SMT solver. The idea behind semantic fusion is to fuse formula pairs of
the same satisfiability (both either sat or unsat) and so produce mutant
formulas of known satisfiability.

*** Example 1 (basic usage):

The following command runs yinyang on the the SMT solver z3 with pre-categorized
seed formulas [1] and shows its expected behavior.

    $ yinyang -o sat "z3 model_validate=true" semantic-fusion-seeds/QF_NRA/sat
    [2021/06/18 11:25:14 AM] Strategy: yinyang, 1 testing targets, 19228225 seeds
    [2021/06/18 11:25:14 AM] Performed 0 solver calls (0.0 calls/s, eff: NaN, 0.0 mutants/s)
    [2021/06/18 11:25:22 AM] Performed 2 solver calls (0.2 calls/s, eff: 50.0%, 0.1 mutants/s)
    [2021/06/18 11:25:30 AM] Performed 4 solver calls (0.2 calls/s, eff: 50.0%, 0.1 mutants/s)
    [2021/06/18 11:25:38 AM] Performed 6 solver calls (0.2 calls/s, eff: 50.0%, 0.1 mutants/s)
    [2021/06/18 11:25:47 AM] Performed 12 solver calls (0.4 calls/s, eff: 66.7%, 0.2 mutants/s)
    [2021/06/18 11:25:55 AM] Performed 14 solver calls (0.3 calls/s, eff: 64.3%, 0.2 mutants/s)
    User interrupt
    16 seeds processed, 16 valid, 0 invalid
    0 bug triggers found

This will by default randomly select smt2 files from `./semantic-fusion-seeds/QF_NRA/sat`
and generate 30 mutants per file. If a bug has been found, yinyang will store it
in `./bugs`.  You can terminate yinyang by CTLR + C. yinyang stores bug trigger in
./bugs and creates rolling logs up to 5MB per run in ./logs. Note, if you run yinyang
many times in a row, it might be worthwhile to disable logging to avoid an overflow
of the logs directory.

Every five seconds, yinyang will generate statistics on (1) solver calls,
(2) efficiency and (3) mutants per second. Efficiency corresponds to the percentage
of solver calls that did not timeout, cause parser or unsupported option errors.
It is expected that efficiency, solver calls and mutants per second can vary
quite a bit during a regular run of opfuzz. However, if the efficiency is
very low (e.g., < 30%), it may be a good idea to inspect the logs, see what
is going on and potentially adjust seed set and solver commandlines. Note, some
SMT solvers need options to support a particular set of seeds. E.g, cvc5 needs
the option "--strings-exp" to support string logic. Otherwise it will often
throw an error message.

[1] https://github.com/testsmt/semantic-fusion-seeds


"""  # noqa: E501


options = """
options:
    -o {sat,unsat}, --oracle {sat,unsat}
            oracle for fusion. Should match with the provided seed files
            (default: sat)
    -i <N>,  --iterations <N>
            iterations per seed (default: 30)
    -l <path>, --logfolder <path>
            log folder (default: ./logs)
    -t <secs>, --timeout <secs>
            timeout per SMT solver call in seconds (default: 8)
    -b <path>, --bugsfolder <path>
            set bug folder (default: ./bugs)
    -s <path>, --scratchfolder <path>
            temp folder to dump mutants. (default: ./scratch)
    -c <file>, --config <file>
            set custom fusion function file
    -L <bytes>, --limit <bytes>
            file size limit on seed formula in bytes (default: 100000)
    -n, --no-log    disable logging
    -q, --quiet     do not print statistics and other output
    -v, --version   show version number and exit
    -h, --help      show this help message and exit
"""
