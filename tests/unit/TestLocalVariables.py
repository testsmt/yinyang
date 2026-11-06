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
import unittest

from yinyang.src.base.Utils import deepcopy_safe
from yinyang.src.parsing.Ast import Term
from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Typechecker import typecheck
from yinyang.src.parsing.Types import INTEGER_TYPE, BOOLEAN_TYPE
from yinyang.src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import (
    GenTypeAwareMutation
)
from yinyang.src.mutators.GenTypeAwareMutation.Util import (
    binder_types, free_symbols, get_all_subterms, get_unique_subterms,
    visible_symbols
)


class Mockargs:
    config = "yinyang/config/typefuzz_config.txt"


# Lets binding the same name to different sorts, a quantified variable,
# and a quantified variable shadowing a global of another sort.
LOCALS = """
(declare-fun x () Int)
(declare-fun a () (Array Int Int))
(assert (let ((c (+ x 1))) (> c 2)))
(assert (let ((c (store a 0 x))) (= (select c 1) x)))
(assert (forall ((y Int)) (=> (> y x) (> (* y 2) x))))
(assert (exists ((x Bool)) (and x (> 1 0))))
(check-sat)
"""

# Symbols declared after an assert or inside a popped assertion level.
GLOBALS = """
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (> (f x) 0))
(push 1)
(declare-fun g (Int) Int)
(declare-fun y () Int)
(assert (< (g y) (f x)))
(pop 1)
(declare-fun z () Int)
(assert (= (f z) (+ z 1)))
(check-sat)
"""


def find(script, text):
    """:returns: the first subterm of an assert of script printed as text"""
    av_expr, _ = get_all_subterms(script)
    return next(t for t in av_expr if str(t) == text)


class LocalVariableMutationTestCase(unittest.TestCase):
    def parse(self, formula):
        script, glob = parse_str(formula)
        typecheck(script, glob)
        return script

    def test_binder_types(self):
        script = self.parse(LOCALS)
        self.assertEqual(binder_types(find(script, "(> c 2)")),
                         {"c": INTEGER_TYPE})
        self.assertEqual(str(binder_types(find(script, "(select c 1)"))["c"]),
                         "(Array Int Int)")
        self.assertEqual(binder_types(find(script, "(* y 2)")),
                         {"y": INTEGER_TYPE})
        self.assertEqual(binder_types(find(script, "(and x (> 1 0))")),
                         {"x": BOOLEAN_TYPE})
        self.assertEqual(binder_types(script.assert_cmd[0].term), {})

    def test_free_symbols(self):
        script = self.parse(LOCALS)
        self.assertEqual(free_symbols(script.assert_cmd[0].term),
                         ({"x": INTEGER_TYPE}, set()))
        self.assertEqual(free_symbols(find(script, "(> c 2)")),
                         ({"c": INTEGER_TYPE}, set()))
        self.assertEqual(free_symbols(script.assert_cmd[3].term), ({}, set()))
        script = self.parse(GLOBALS)
        variables, functions = free_symbols(find(script, "(< (g y) (f x))"))
        self.assertEqual(set(variables), {"x", "y"})
        self.assertEqual(functions, {"f", "g"})

    def test_visible_symbols(self):
        script = self.parse(GLOBALS)
        visible, declared = visible_symbols(script.commands)
        self.assertEqual(declared, {"f", "g", "x", "y", "z"})
        self.assertEqual(
            [visible[id(cmd.term)] for cmd in script.assert_cmd],
            [{"f", "x"}, {"f", "g", "x", "y"}, {"f", "x", "z"}],
        )

    def check_scoping(self, script):
        """
        Each variable of each assert is bound with its type by an enclosing
        quantifier or let, or declared before the assert and not popped.
        """
        visible, _ = visible_symbols(script.commands)
        for cmd in script.assert_cmd:
            for t in get_all_subterms_of(cmd.term):
                env = binder_types(t)
                if t.is_var:
                    if t.name in env:
                        self.assertEqual(env[t.name], t.type, str(cmd))
                    else:
                        self.assertIn(t.name, visible[id(cmd.term)],
                                      str(cmd))
                if isinstance(t.op, Term):
                    self.assertNotIn(t.op.name, env, str(cmd))
                    self.assertIn(t.op.name, visible[id(cmd.term)],
                                  str(cmd))

    def test_mutants_well_scoped(self):
        # typefuzz used to move let- and quantifier-bound variables out of
        # their scope, to put a let variable where the same name is bound
        # to another sort, and to use symbols before their declaration or
        # after the pop of their assertion level.
        for formula in [LOCALS, GLOBALS]:
            for seed in range(20):
                random.seed(seed)
                script = self.parse(formula)
                unique_expr = get_unique_subterms(deepcopy_safe(script))
                gen = GenTypeAwareMutation(script, Mockargs(), unique_expr)
                for _ in range(10):
                    gen.mutate()
                    self.check_scoping(script)
                self.parse(str(script))

    def test_named_terms(self):
        # Copies of a term with a :named attribute would define the name
        # twice, or inside a quantifier.
        formula = """
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (assert (! (and p (not q)) :named h1))
        (assert (forall ((b Bool)) (or b (! (or p q) :named h2))))
        (check-sat)
        """
        for seed in range(20):
            random.seed(seed)
            script = self.parse(formula)
            unique_expr = get_unique_subterms(deepcopy_safe(script))
            gen = GenTypeAwareMutation(script, Mockargs(), unique_expr)
            for _ in range(10):
                gen.mutate()
                mutant = str(script)
                self.assertLessEqual(mutant.count(":named h1"), 1, mutant)
                self.assertLessEqual(mutant.count(":named h2"), 1, mutant)

    def test_parent_pointers(self):
        # After a substitution, the new subterms point to the term they
        # replaced and not to a copy of the term they come from.
        script = self.parse(LOCALS)
        hole = find(script, "(> c 2)")
        repl = find(script, "(= (select c 1) x)")
        hole.substitute(hole, repl)
        for t in get_all_subterms_of(script.assert_cmd[0].term):
            for sub in t.subterms or []:
                self.assertIs(sub.parent, t)


def get_all_subterms_of(term):
    yield term
    for sub in term.subterms or []:
        yield from get_all_subterms_of(sub)


if __name__ == "__main__":
    unittest.main()
