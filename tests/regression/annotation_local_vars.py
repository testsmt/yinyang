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

sys.path.append("../../")

from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Typechecker import typecheck

# Annotated terms (! t attr) must be parsed with the enclosing local
# variables, both at top level and under a binder.
script, glob = parse_str("""\
(declare-fun b () Bool)
(assert (! b :named n))
(check-sat)""")
assert script is not None
typecheck(script, glob)

script, glob = parse_str("""\
(declare-sort U 0)
(declare-fun p (U) Bool)
(assert (forall ((x U)) (! (p x) :pattern ((p x)))))
(check-sat)""")
assert script is not None
typecheck(script, glob)

script, glob = parse_str("""\
(define-fun-rec f ((x Bool)) Bool (not x))
(assert (f true))
(check-sat)""")
assert script is not None
