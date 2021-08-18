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

import unittest
import sys

sys.path.append("../../")
import os

from yinyang.src.parsing.Parse import *
from yinyang.src.parsing.Typechecker import Context, typecheck
from yinyang.src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import *
from yinyang.src.mutators.GenTypeAwareMutation.Util import *


class Mockargs:
    modulo = 3
    config = "yinyang/config/typefuzz_config.txt"


class GenTypeAwareMutationTestCase(unittest.TestCase):
    def test_ta(self):
        formulafile = "formula.smt2"
        formula = """
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (> (* (+ 3 x) (- y 2)) (div 5 z)))
        (assert (= (+ 7 y) x))
        (assert (< 6 (div (+ 4 x) z)))
        (check-sat)
        """
        with open(formulafile, "w") as f:
            f.write(formula)
        script, glob = parse_str(formula)
        typecheck(script, glob)
        args = Mockargs()
        args.name = formulafile.strip(".smt2")
        script, glob = parse_file(formulafile, silent=True)
        typecheck(script, glob)
        self.av_expr, self.expr_type = get_all_subterms(script)
        unique_expr = get_unique_subterms(script)
        gen = GenTypeAwareMutation(script, args, unique_expr)
        gen.generate()
        os.system("rm " + formulafile)


if __name__ == "__main__":
    unittest.main()
