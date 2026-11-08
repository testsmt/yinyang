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
import sys
import unittest

from yinyang.src.parsing.Parse import parse_str, parse_file
from yinyang.src.mutators.TypeAwareOpMutation import TypeAwareOpMutation

sys.path.append("../../")


class Mockargs:
    config = ""
    scratchfolder = "."
    name = ""


class TypeAwareOpMutationTestCase(unittest.TestCase):
    def test_ta(self):
        configfile = "tests/res/operators.txt"
        formulafile = "tests/res/formula_file.smt2"
        script, _ = parse_file(formulafile)

        args = Mockargs()
        args.config = configfile
        args.name = formulafile.strip(".smt2")
        args.config = configfile
        args.modulo = 2

        script, _ = parse_file(formulafile, silent=True)
        mutator = TypeAwareOpMutation(script, args)
        mutator.mutate()

    def mutants(self, formula, n=300):
        args = Mockargs()
        args.config = "yinyang/config/operator_mutations.txt"
        args.modulo = 1
        mutants = set()
        for i in range(n):
            random.seed(i)
            script, _ = parse_str(formula)
            mutant, success, _ = TypeAwareOpMutation(script, args).mutate()
            if success:
                mutants.add(str(mutant).split("\n")[-1])
        return mutants

    def test_arity(self):
        # Operators are only replaced by operators that accept the same
        # number of arguments: bvashr, bvsub, ... and mod are binary.
        bv = ["bvand", "bvor", "bvxor", "bvadd", "bvmul"]
        mutants = self.mutants(
            "(declare-const a (_ BitVec 8))(declare-const b (_ BitVec 8))"
            "(assert (= a (bvadd a b a)))")
        self.assertEqual(mutants, {"(assert (= a (%s a b a)))" % op
                                   for op in bv if op != "bvadd"}
                         | {"(assert (distinct a (bvadd a b a)))"})
        mutants = self.mutants(
            "(declare-const x Int)(assert (= x (div x 2 3)))")
        self.assertEqual(mutants, {"(assert (distinct x (div x 2 3)))"})
        mutants = self.mutants(
            "(declare-const x Int)(assert (> x (- x 1)))")
        self.assertNotIn("(assert (> x (abs x 1)))", mutants)
        self.assertIn("(assert (> x (* x 1)))", mutants)
        mutants = self.mutants(
            "(declare-const x Int)(assert (> x (- x)))")
        self.assertIn("(assert (> x (abs x)))", mutants)

    def test_unidirectional_and_quantifiers(self):
        mutants = self.mutants(
            "(declare-const p Bool)(assert (not p))", n=50)
        self.assertEqual(mutants, {"(assert (and p))", "(assert (or p))"})
        mutants = self.mutants(
            "(declare-const x Int)(assert (exists ((y Int)) (> y x)))")
        self.assertIn("(assert (forall ((y Int)) (> y x)))", mutants)


if __name__ == "__main__":
    unittest.main()
