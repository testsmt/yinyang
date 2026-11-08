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

from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Typechecker import typecheck
from yinyang.src.parsing.Cvc5 import cvc5_unsupported
from yinyang.src.mutators.TypeAwareOpMutation import TypeAwareOpMutation
from yinyang.src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import (
    GenTypeAwareMutation
)
from yinyang.src.mutators.GenTypeAwareMutation.Util import (
    get_unique_subterms
)

sys.path.append("../../")

DECLS = (
    "(declare-const x String)(declare-const y String)"
    "(declare-const r RegLan)(declare-const r2 RegLan)"
    "(declare-fun f (Int) String)"
)

A = '(str.to_re "a")'


class Mockargs:
    modulo = 1
    cvc5_compat = True


class Cvc5TestCase(unittest.TestCase):
    def check(self, asserts):
        script, _ = parse_str(DECLS + asserts)
        return cvc5_unsupported(script)

    def test_re_range(self):
        # Accepted and rejected by cvc5 1.4.2.
        for ok in ['(re.range "a" "c")', '(re.range (str.++ "a" "") "c")',
                   '(re.range (str.from_code 97) "c")',
                   '(let ((a "a")) (re.range a "c"))']:
            self.assertIsNone(
                self.check("(assert (str.in_re x %s))" % ok), ok)
        for bad in ['(re.range x "c")', '(re.range (f 1) "c")',
                    '(re.range (str.from_code (str.len x)) "c")',
                    '(let ((a x)) (re.range a "c"))']:
            self.assertIsNotNone(
                self.check("(assert (str.in_re x %s))" % bad), bad)
        self.assertIsNotNone(self.check(
            '(assert (exists ((z String)) (str.in_re x (re.range z "c"))))'))

    def test_reglan(self):
        # Accepted by cvc5 1.4.2: each RegLan constant is eliminated.
        for ok in [
            "(assert (= r %s))(assert (str.in_re x r))" % A,
            "(assert (= %s r))(assert (str.in_re x r))" % A,
            "(assert (and (= r %s) (str.in_re x r)))" % A,
            "(assert (= r %s))(assert (str.in_re x (re.comp r)))" % A,
            "(assert (= r (re.* r2)))(assert (= r2 %s))"
            "(assert (str.in_re x r))" % A,
            "(assert (= r %s))(assert (= r r2))(assert (str.in_re x r2))" % A,
            "(assert (= r (re.* (str.to_re y))))(assert (str.in_re x r))",
            "(assert (str.in_re x %s))" % A,  # r is not used
        ]:
            self.assertIsNone(self.check(ok), ok)
        # Rejected by cvc5 1.4.2 with "Regular expression variables are not
        # supported".
        for bad in [
            "(assert (str.in_re x r))",
            "(assert (distinct r %s))(assert (str.in_re x r))" % A,
            "(assert (= r (re.* r)))(assert (str.in_re x r))",
            "(assert (= r r2))(assert (str.in_re x r2))",
            "(assert (= r %s))(assert (= r (re.comp r2)))"
            "(assert (str.in_re x r2))" % A,
            "(assert (or (= r %s) (= r re.none)))(assert (str.in_re x r))"
            % A,
            "(assert (= r %s))(assert (exists ((q RegLan)) (str.in_re x q)))"
            % A,
        ]:
            self.assertIsNotNone(self.check(bad), bad)
        script, _ = parse_str(
            "(declare-fun g (Int) RegLan)"
            "(assert (str.in_re \"a\" (g 1)))")
        self.assertIsNotNone(cvc5_unsupported(script))

    SEED = (
        "(declare-const x String)(declare-const r RegLan)"
        "(assert (= r (re.+ (re.range \"0\" \"9\"))))"
        "(assert (str.in_re x r))"
        "(assert (= (str.len x) 3))"
    )

    def test_opfuzz(self):
        # = -> distinct on the definition of r is undone, other mutations
        # are kept.
        args = Mockargs()
        args.config = "yinyang/config/operator_mutations.txt"
        mutated = 0
        for i in range(100):
            random.seed(i)
            script, _ = parse_str(self.SEED)
            mutant, success, _ = TypeAwareOpMutation(script, args).mutate()
            self.assertIsNone(cvc5_unsupported(mutant))
            mutated += success
        self.assertGreater(mutated, 0)
        # Without the option, opfuzz does generate such mutants.
        args.cvc5_compat = False
        rejected = 0
        for i in range(100):
            random.seed(i)
            script, _ = parse_str(self.SEED)
            mutant, _, _ = TypeAwareOpMutation(script, args).mutate()
            rejected += cvc5_unsupported(mutant) is not None
        self.assertGreater(rejected, 0)

    def test_typefuzz(self):
        args = Mockargs()
        args.config = "yinyang/config/typefuzz_config.txt"
        mutated = 0
        for i in range(100):
            random.seed(i)
            script, glob = parse_str(self.SEED)
            typecheck(script, glob)
            mutator = GenTypeAwareMutation(
                script, args, get_unique_subterms(script))
            for _ in range(3):  # mutations accumulate in typefuzz
                mutant, success, _ = mutator.mutate()
                self.assertIsNone(cvc5_unsupported(mutant), str(mutant))
                mutated += success
        self.assertGreater(mutated, 0)
        # Without the option, typefuzz does generate such mutants.
        args.cvc5_compat = False
        rejected = 0
        for i in range(100):
            random.seed(i)
            script, glob = parse_str(self.SEED)
            typecheck(script, glob)
            mutator = GenTypeAwareMutation(
                script, args, get_unique_subterms(script))
            for _ in range(3):
                mutant, _, _ = mutator.mutate()
            rejected += cvc5_unsupported(mutant) is not None
        self.assertGreater(rejected, 0)


if __name__ == "__main__":
    unittest.main()
