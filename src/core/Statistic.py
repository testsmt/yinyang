# MIT License
#
# Copyright (c) [2020 - 2020] The yinyang authors
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

import time
import logging


class Statistic:
    def __init__(self):
        self.starttime = time.time()
        self.total_seeds = 0
        self.invalid_seeds = 0
        self.total_generations = 0
        self.unsuccessful_generations = 0
        self.mutants = 0
        self.invalid_mutants = 0
        self.crashes = 0
        self.soundness = 0
        self.duplicates = 0
        self.timeout = 0
        self.solver_calls = 0
        self.effective_calls = 0

    def printbar(self, start_time):
        total_time = time.time() - start_time
        if self.solver_calls != 0:
            eff = round(
                (float(self.effective_calls) / float(self.solver_calls)) * 100,
                1
            )
            eff_str = str(eff) + "%"
        else:
            eff_str = "NaN"

        solver_calls_per_sec = round(
            float(self.solver_calls) / float(total_time), 1)

        mutants_per_sec = round(float(self.mutants) / float(total_time), 1)
        mutants_per_sec_str = str(mutants_per_sec)
        bar = "Performed %d solver calls \
(%s calls/s, eff: %s, %s mutants/s)" % (
            self.solver_calls,
            solver_calls_per_sec,
            eff_str,
            mutants_per_sec_str,
        )
        logging.info(bar)

    def printsum(self):
        valid_seeds = self.total_seeds - self.invalid_seeds
        num_bugs = self.crashes + self.soundness
        summary = (
            "\b\b%d seeds processed, \
%d valid, %d invalid \n%d bug triggers found"
            % (self.total_seeds, valid_seeds, self.invalid_seeds, num_bugs)
        )
        print(summary)
