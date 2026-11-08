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
import signal
import pathlib

from yinyang.src.base.Utils import in_list, load_config

crash_list = load_config("crash_list")
duplicate_list = load_config("duplicate_list")
ignore_list = load_config("ignore_list")

from yinyang.src.core.Solver import SolverResult, SolverQueryResult


def in_crash_list(stdout, stderr):
    return in_list(stdout, stderr, crash_list)


def in_duplicate_list(stdout, stderr):
    return in_list(stdout, stderr, duplicate_list)


def in_ignore_list(stdout, stderr):
    return in_list(stdout, stderr, ignore_list)


# Signals raised by the solver process itself when it crashes. SIGKILL,
# SIGTERM, SIGINT, etc. are left out: they usually come from outside the
# solver (timeouts, the OOM killer, the user).
CRASH_SIGNALS = [
    getattr(signal, name)
    for name in ["SIGSEGV", "SIGABRT", "SIGFPE", "SIGBUS", "SIGILL",
                 "SIGTRAP", "SIGSYS"]
    if hasattr(signal, name)
]


def crash_signal(exitcode):
    """
    Checks whether a solver exit code means the solver died from a crash
    signal. The exit code is -N if the solver was killed by signal N, and
    128 + N if a shell wrapper around the solver reports it. 245 is kept
    as a segfault for backward compatibility.
    :returns: the signal (signal.Signals) or None.
    """
    if exitcode == 245:
        return signal.SIGSEGV
    for sig in CRASH_SIGNALS:
        if exitcode == -sig or exitcode == 128 + sig:
            return signal.Signals(sig)
    return None


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
    num_initial = len(initial_seeds)
    random.shuffle(initial_seeds)

    if strategy == "yinyang":
        assert len(initial_seeds) >= 2
        gen = get_permutation_generator(initial_seeds)
        return gen, num_initial**2
    else:
        assert strategy in ["opfuzz", "typefuzz"]
        return initial_seeds, num_initial


def get_permutation_generator(seeds):
    """
    Yields each ordered pair (a, b) of seeds once, including the pairs of a
    seed with itself. The pairs come in rounds of len(seeds) pairs, in which
    every seed is the first seed of one pair and the second seed of one
    pair, so that all seeds are fused early on: in round k, seed i is
    paired with seed i + k (mod n), for the offsets k = 0..n-1 in random
    order.
    """
    n = len(seeds)
    offsets = list(range(n))
    random.shuffle(offsets)
    for k in offsets:
        order = list(range(n))
        random.shuffle(order)
        for i in order:
            yield seeds[i], seeds[(i + k) % n]


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
