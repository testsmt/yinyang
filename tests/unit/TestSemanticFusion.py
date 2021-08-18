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

import sys
import unittest

from yinyang.src.parsing.Parse import parse_file
from yinyang.src.mutators.SemanticFusion.SemanticFusion import SemanticFusion

sys.path.append("../../")


class Mockargs:
    oracle = ""
    config = ""


class SemanticFusionTestCase(unittest.TestCase):
    def test_sf_sat(self):
        fn1 = "tests/res/formula1.smt2"
        fn2 = "tests/res/formula2.smt2"
        fn_fcts = "tests/res/fusion_functions.txt"

        args = Mockargs()
        args.oracle = "sat"
        args.config = fn_fcts
        script1, _ = parse_file(fn1, silent=True)
        script2, _ = parse_file(fn2, silent=True)
        sf_sat = SemanticFusion(script1, script2, args)
        args.oracle = "unsat"
        script1, _ = parse_file(fn1, silent=True)
        script2, _ = parse_file(fn2, silent=True)
        sf_sat.mutate()


if __name__ == "__main__":
    unittest.main()
