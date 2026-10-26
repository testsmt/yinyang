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

sys.path.append("../../")

from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Typechecker import TypeCheckError, typecheck
from yinyang.src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import (
    GenTypeAwareMutation,
)
from yinyang.src.mutators.GenTypeAwareMutation.Util import (
    get_unique_subterms,
)


class Mockargs:
    modulo = 2
    config = "../../yinyang/config/typefuzz_config.txt"


# Arguments of generated operator applications must not contain variables
# bound by a quantifier outside of that quantifier's scope.
for i in range(40):
    random.seed(i)
    script, glob = parse_str("""\
(declare-sort U 0)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(declare-fun a () U)
(assert (forall ((x U)) (=> (p x) (q x))))
(assert (p a))
(assert (not (q a)))
(check-sat)""")
    typecheck(script, glob)
    gen = GenTypeAwareMutation(script, Mockargs(), get_unique_subterms(script))
    gen.mutate()
    for cmd in script.assert_cmd:
        s = cmd.__str__()
        if "forall" not in s:
            assert "x" not in s.replace("(", " ").replace(")", " ").split(), s

# Same-named variables of different quantifiers may differ in sort, so a
# subterm using x must not move between the two quantifiers below.
for i in range(40):
    random.seed(i)
    script, glob = parse_str("""\
(declare-fun a () Int)
(assert (forall ((x Int)) (> x a)))
(assert (forall ((x Bool)) (or x (> a 0))))
(check-sat)""")
    typecheck(script, glob)
    gen = GenTypeAwareMutation(script, Mockargs(), get_unique_subterms(script))
    gen.mutate()
    mutant, glob = parse_str(script.__str__())
    try:
        typecheck(mutant, glob)
    except TypeCheckError as e:
        # Other errors come from operators the typechecker does not support
        assert "faulty subterm:\tx\n" not in e.message, e.message
