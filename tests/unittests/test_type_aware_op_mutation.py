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
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
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

from src.parsing.parse import *
from src.generators.TypeAwareOpMutation import TypeAwareOpMutation


class Mockargs:
    opconfig = ""
    scratchfolder = "."
    name = ""

class TypeAwareOpMutationTestCase(unittest.TestCase):

    def test_ta(self):
        configfile="operators.txt"
        formulafile="formula.smt2"
        ops= """
        =,distinct
        exists,forall
        and,or,=>
        <=, >=,<,>
        +,-,*,/ :arity 2+
        div,mod
        """
        with open(configfile,"w") as f:
            f.write(ops)

        formula = """
        (declare-const x Int)
        (declare-const y Int)
        (declare-const w Bool)
        (assert (= x (- x)))
        (assert (distinct w (= x (- y))))
        (assert w)
        (check-sat)
        """
        with open(formulafile,"w") as f:
            f.write(formula)
        script = parse_str(formula)
        args = Mockargs()
        print(formulafile)
        args.name = formulafile.strip(".smt2")
        args.opconfig = configfile
        args.modulo = 2
        script= parse_file(formulafile,silent=True)
        gen = TypeAwareOpMutation(script,args)
        gen.generate()
        os.system("rm -rf "+configfile+ " "+ formulafile)



if __name__ == '__main__':
    #TypeAwareOpMutationTestCase.test_ta()
    unittest.main()

