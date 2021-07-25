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

from src.parsing.Parse import parse_str, parse_file

sys.path.append("../../")


# Dominik: These are all regression. If these become more, it would make sense
# to put them their own folder.
class ParsingTestCase(unittest.TestCase):
    def test_issue9(self):
        formula, _ = parse_file("tests/res/issue7.smt2")
        self.assertTrue(
            "\x0a" in formula.__str__() and "\n" in formula.__str__())

    def test_issue18(self):
        formula, _ = parse_file("tests/res/issue18.smt2", silent=False)
        oracle = """\
(declare-fun a () String)
(declare-fun b () String)
(assert (= a b))
(check-sat)
(assert (= a b))
(check-sat)"""
        self.assertEqual(oracle, formula.__str__())


#     def test_issue25(self):
# script = """\
# (declare-fun a () Bool)
# (assert (= ((_ extract 5 3) (_ bv96 8))))
# (check-sat)"""
# script, _ = parse_str(script, silent=False)
# t = type(script.commands[1].term.subterms[0].subterms[0])
# self.assertTrue("Term" in str(t))
# script = """\
# (declare-fun bv () (_ BitVec 10))
# (declare-fun a () Bool)
# (assert (not (and (= ((_ extract 5 3) (_ bv96 8)) ((_ extract 4 2)
# (concat (_ bv121 7)((_ extract 0 0) bv)))) (= (concat (_ bv1 1) (ite a
# (_ bv0 1) (_ bv1 1))) ((_ extract 1 0)
# (ite a (_ bv6 3) (_ bv3 3)))))))
# (check-sat)"""
# script, _ = parse_str(script, silent=False)
# self.assertTrue(script)


if __name__ == "__main__":
    unittest.main()
