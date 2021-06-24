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
import sys
import unittest

from src.parsing.Parse import parse_file
from src.mutators.SemanticFusion.SemanticFusion import SemanticFusion

sys.path.append("../../")


class Mockargs:
    oracle = ""
    fusionfun = "."


class SemanticFusionTestCase(unittest.TestCase):
    def test_sf_sat(self):
        fcts = """
        #begin
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (declare-const c Int)
        (assert (= z (+ x c) y))
        (assert (= x (- (- z c) y)))
        (assert (= y (- (- z c) x)))
        #end
        """
        formula1 = """
        (declare-const x Int)
        (assert (= x (- 1)))
        """
        formula2 = """
        (declare-const y Int)
        (declare-const v Bool)
        (assert (= v (not (= y (- 1)))))
        (assert (ite v false (= y (- 1))))
        (check-sat)
        """
        fn1, fn2, fn_fcts = "formula1.smt2", "formula2.smt2", "fcts.txt"
        with open(fn_fcts, "w") as f1:
            f1.write(fcts)
        with open(fn1, "w") as f1:
            f1.write(formula1)
        with open(fn2, "w") as f2:
            f2.write(formula2)
        args = Mockargs()
        args.oracle = "sat"
        args.fusionfun = "./config/fusion_functions.txt"
        script1 = parse_file(fn1, silent=True)
        script2 = parse_file(fn2, silent=True)
        sf_sat = SemanticFusion(script1, script2, args)
        args.oracle = "unsat"

        script1 = parse_file(fn1, silent=True)
        script2 = parse_file(fn2, silent=True)
        sf_sat.generate()
        os.system("rm -rf " + fn1 + " " + fn2 + " " + fn_fcts)


if __name__ == "__main__":
    # SemanticFusionTestCase().test_sf_sat()
    unittest.main()
