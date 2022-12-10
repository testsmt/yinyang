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
import random
import re
import pathlib

from yinyang.src.base.Utils import in_list

try:
    sys.path.insert(1, os.getcwd() + "/.yinyang")
    from yinyang.config import crash_list, duplicate_list, ignore_list
except Exception as e:
    from yinyang.config.Config import crash_list, duplicate_list, ignore_list

from yinyang.src.core.Solver import SolverResult, SolverQueryResult


def in_crash_list(stdout, stderr):
    return in_list(stdout, stderr, crash_list)


def in_duplicate_list(stdout, stderr):
    return in_list(stdout, stderr, duplicate_list)


def in_ignore_list(stdout, stderr):
    return in_list(stdout, stderr, ignore_list)


def admissible_seed_size(seed, args):
    """
    Checks if seed size is below file_size_limit.
    :returns: True if that is the case and False otherwise.
    """
    seed_size_in_bytes = pathlib.Path(seed).stat().st_size
    return seed_size_in_bytes < args.file_size_limit


def grep_result(stdout):
    """
    Grep the result from the stdout of a solver.
    """
    result = SolverResult()
    for line in stdout.splitlines():
        if re.search("^unsat$", line, flags=re.MULTILINE):
            result.append(SolverQueryResult.UNSAT)
        elif re.search("^sat$", line, flags=re.MULTILINE):
            result.append(SolverQueryResult.SAT)
        elif re.search("^unknown$", line, flags=re.MULTILINE):
            result.append(SolverQueryResult.UNKNOWN)
    return result


def get_seeds(args, strategy):
    initial_seeds = args.PATH_TO_SEEDS

    if args.randomize:
        random.shuffle(initial_seeds)

    if strategy == "yinyang":
        assert len(initial_seeds) >= 2
        return [(a, b) for a in initial_seeds for b in initial_seeds]
    else:
        assert strategy in ["opfuzz", "typefuzz"]
        return initial_seeds


def init_oracle(args):
    """
    Initialize the oracle. For SemanticFusion the oracle is either sat or
    unsat. For TypeAwareOpMutation the oracle is unknown
    """
    if args.oracle == "unknown":
        return SolverResult(SolverQueryResult.UNKNOWN)
    elif args.oracle == "sat":
        return SolverResult(SolverQueryResult.SAT)
    elif args.oracle == "unsat":
        return SolverResult(SolverQueryResult.UNSAT)
    assert False
