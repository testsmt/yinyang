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
    PATH_TO_SEEDS = ["a.smt2", "b.smt2", "c.smt2"]
    SOLVER_CLIS = []
    iterations = 3
    quiet = True
    keep_mutants = True  # read by Fuzzer.__del__


class Boom:
    def mutate(self):
        raise RecursionError("maximum recursion depth exceeded")


class Unsuccessful:
    def __init__(self, calls):
        self.calls = calls

    def mutate(self):
        self.calls.append(1)
        return None, False, False


class SeedErrorsTestCase(unittest.TestCase):
    def test_errors_do_not_stop_the_run(self):
        # An error in yinyang while preparing or mutating one seed skips
        # that seed; the other seeds are still processed.
        fuzzer = Fuzzer.__new__(Fuzzer)
        fuzzer.args = Args()
        fuzzer.strategy = "typefuzz"
        fuzzer.statistic = Statistic()
        fuzzer.start_time = fuzzer.old_time = time.time()
        fuzzer.first_status_bar_printed = True
        calls = []

        def init_mutator(seed):
            fuzzer.statistic.total_seeds += 1
            if seed == "a.smt2":
                raise KeyError("Int")
            fuzzer.mutator = Boom() if seed == "b.smt2" \
                else Unsuccessful(calls)
            return True

        fuzzer.init_mutator = init_mutator
        with self.assertLogs(level="ERROR") as logs, \
                redirect_stdout(io.StringIO()), \
                self.assertRaises(SystemExit):
            fuzzer.run()
        self.assertEqual(logs.output, [
            "ERROR:root:Skip seed a.smt2: error in yinyang while "
            "preparing: KeyError: 'Int'",
            "ERROR:root:Skip seed b.smt2: error in yinyang while "
            "mutating: RecursionError: maximum recursion depth exceeded",
        ])
        self.assertEqual(fuzzer.statistic.total_seeds, 3)
        self.assertEqual(fuzzer.statistic.failed_seeds, 1)
        self.assertEqual(fuzzer.statistic.invalid_seeds, 1)
        self.assertEqual(fuzzer.statistic.mutator_errors, 1)
        self.assertEqual(len(calls), Args.iterations)


if __name__ == "__main__":
    unittest.main()
