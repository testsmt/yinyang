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
import io
import time
import unittest
from contextlib import redirect_stdout

from yinyang.src.core.Fuzzer import Fuzzer
from yinyang.src.core.Statistic import Statistic


class Args:
    PATH_TO_SEEDS = ["a.smt2", "b.smt2"]
    SOLVER_CLIS = []
    iterations = 10
    quiet = True
    keep_mutants = True  # read by Fuzzer.__del__
    div_by_zero = "nonlinear"


class Mutator:
    def mutate(self):
        return "mutant", True, False


class ConsecutiveTimeoutsTestCase(unittest.TestCase):
    def run_fuzzer(self, limit, timeouts):
        """
        timeouts: seed -> the iterations (from 1) on which a solver times out

        :returns: seed -> the iterations that were tested
        """
        fuzzer = Fuzzer.__new__(Fuzzer)
        fuzzer.args = Args()
        fuzzer.args.consecutive_timeouts = limit
        fuzzer.strategy = "typefuzz"
        fuzzer.statistic = Statistic()
        fuzzer.start_time = fuzzer.old_time = time.time()
        fuzzer.first_status_bar_printed = True
        fuzzer.logic_base = None
        fuzzer.seed_logic = None
        tested = {}

        def init_mutator(seed):
            fuzzer.seed = seed
            fuzzer.mutator = Mutator()
            return True

        def test(mutant, iteration):
            tested.setdefault(fuzzer.seed, []).append(iteration)
            if iteration in timeouts.get(fuzzer.seed, ()):
                fuzzer.timeout_of_current_seed += 1
            return True, None

        fuzzer.init_mutator = init_mutator
        fuzzer.test = test
        with redirect_stdout(io.StringIO()), self.assertRaises(SystemExit):
            fuzzer.run()
        return tested, fuzzer.statistic.timeout_seeds

    def test_consecutive_timeouts(self):
        timeouts = {"a.smt2": [1, 3, 4, 5], "b.smt2": [2, 4, 6, 8]}
        tested, skipped = self.run_fuzzer(2, timeouts)
        # a: the timeouts on 3 and 4 skip the rest of a; b has no two
        # consecutive timeouts.
        self.assertEqual(tested["a.smt2"], [1, 2, 3, 4])
        self.assertEqual(tested["b.smt2"], list(range(1, 11)))
        self.assertEqual(skipped, 1)
        # 0 never skips.
        tested, skipped = self.run_fuzzer(0, timeouts)
        self.assertEqual(tested["a.smt2"], list(range(1, 11)))
        self.assertEqual(skipped, 0)


if __name__ == "__main__":
    unittest.main()
