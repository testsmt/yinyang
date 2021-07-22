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

from src.base.Version import VERSION


header = (
    "typefuzz -- a differential fuzzer for SMT solvers [version: "
    + VERSION
    + "]"
)

usage = """ typefuzz [options] solver_clis seed_file   [optionally, more seed files]
       typefuzz [options] solver_clis seed_folder [optionally, more seed folders]
       solver_clis := "solver_cli1;solver_cli2;...;solver_clik"
"""  # noqa: E501

short_description = """
typefuzz is a tool for finding bugs in SMT solver by generating mutant SMT-LIB
scripts from a set of seed SMT-LIB scripts (.smt2 files) and then cross-check
the results of the solvers. typefuzz realizes generative type-aware operator
mutations.

Example (basic usage):
$ typefuzz "z3 model_validate=true;cvc5 --check-models -m -i -q" benchmarks
[2021/06/10 12:12:40 PM] Strategy: typefuzz, 2 testing targets, 299476 seeds
[2021/06/10 12:12:41 PM] Performed 36 solver calls (35.1 calls/s, eff: 88.9%, 17.6 mutants/s)
[2021/06/10 12:12:46 PM] Performed 254 solver calls (41.9 calls/s, eff: 95.3%, 21.0 mutants/s)
User interrupt
1 seeds processed, 1 valid, 0 invalid
0 bug triggers found

This will by default randomly select smt2 files from the folder `./benchmarks`
and generate 300 mutants per file. If a bug has been found, typefuzz will store
it in `./bugs`. You can use the shortcut CTRL+C to terminate typefuzz manually.
For a listing of options and further information, use typefuzz --help."""   # noqa: E501

long_description = """
typefuzz is a mutation-based fuzzer, i.e. it mutates a set of seed formulas using
generative type-aware mutation then uses the mutated formulas as the test
seeds for SMT solvers. It can so detect soundness bugs, invalid model bugs,
crashes, segfaults, etc. typefuzz's mutation strategy generates mutants by
generating, fresh expressions from the ones from the seed and root them by
operators such as , =, distinct, +, -,  *, / by one another. typefuzz
is based on differential testing, i.e. it needs at least two SMT solvers to
compare their results.

*** Example 1 (basic usage) ***

The following command runs typefuzz on the two SMT solver z3 and cvc5 with seed
formulas from the folder "benchmarks" and shows its expected behavior.

    $ typefuzz "z3 model_validate=true;cvc5 --check-models -m -i -q" benchmarks
    [2021/06/10 11:07:39 AM] Strategy: typefuzz, 2 testing targets, 299476 seeds
    [2021/06/10 11:07:40 AM] Performed 108 solver calls (107.5 calls/s, eff: 100.0%, 53.8 mutants/s)
    [2021/06/10 11:07:45 AM] Performed 630 solver calls (104.5 calls/s, eff: 98.1%, 52.2 mutants/s)
    [2021/06/10 11:07:50 AM] Performed 782 solver calls (70.6 calls/s, eff: 89.0%, 35.3 mutants/s)
    [2021/06/10 11:07:55 AM] Performed 936 solver calls (58.2 calls/s, eff: 82.6%, 29.1 mutants/s)
    [2021/06/10 11:08:00 AM] Performed 1090 solver calls (51.6 calls/s, eff: 78.3%, 25.8 mutants/s)
    [2021/06/10 11:08:20 AM] Performed 1202 solver calls (29.5 calls/s, eff: 76.3%, 14.8 mutants/s)
    [2021/06/10 11:08:30 AM] Performed 1204 solver calls (23.8 calls/s, eff: 76.2%, 11.9 mutants/s)
    User interrupt
    3 seeds processed, 3 valid, 0 invalid
    0 bug triggers found

typefuzz randomly selects the seed formulas from the folder and, by default,
ignores files larger than 100k. typefuzz will generate 300 mutants per seed
formula, with which it tests the SMT solvers. You can terminate typefuzz by CTLR + C.
typefuzz stores bug trigger in ./bugs and creates rolling logs up to 5MB per run
in ./logs. Note, if you run typefuzz many times in a row, it might be worthwhile
to disable logging to avoid an overflow of the logs directory.

Every two seconds, typefuzz will generate statistics on (1) solver calls,
(2) efficiency and (3) mutants per second. Efficiency corresponds to the percentage
of solver calls that did not timeout, cause parser or unsupported option errors.
It is expected that efficiency, solver calls and mutants per second can vary
quite a bit during a regular run of typefuzz. However, if the efficiency is
very low (e.g., < 50%), it may be a good idea to inspect the logs, see what
is going on and potentially adjust seed set and solver commandlines. Note, some
SMT solvers need options to support a particular set of seeds. E.g, cvc5 needs
the option "--strings-exp" to support string logic. Otherwise it will often
throw an error message.
"""  # noqa: E501


options = """
options:
    -i <N>,  --iterations <N>
            iterations per seed (default: 300)
    -m <N>,  --modulo <N>
            the number of times the seed will be forwarded to the solvers
            For example, with 300 iterations and 2 as a modulo, 150 mutants
            per seed file will be passed to the SMT solvers (default: 2)
    -l <path>, --logfolder <path>
            log folder (default: ./logs)
    -t <secs>, --timeout <secs>
            timeout per SMT solver call in seconds (default: 8)
    -b <path>, --bugsfolder <path>
            set bug folder (default: ./bugs)
    -s <path>, --scratchfolder <path>
            temp folder to dump mutants (default: ./scratch)
    -c <file>, --config <file>
            set custom config file. (default: config/typefuzz_config.txt)
    -L <bytes>, --limit <bytes>
            file size limit on seed formula in bytes (default: 100000)
    -n, --no-log    disable logging
    -q, --quiet     do not print statistics and other output
    -v, --version   show version number and exit
    -h, --help      show this help message and exit
"""
