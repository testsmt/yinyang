import unittest
import os
import sys
sys.path.append("../../")

from src.parsing.parse import *

# Dominik: These are all regression. If these become more, it would make sense
# to put them their own folder.
class ParsingTestCase(unittest.TestCase):
    def test_issue9(self):
        formula = parse_file("tests/unittests/issue7.smt2")
        self.assertTrue('\x0a' in formula.__str__() and '\n' in formula.__str__())

    def test_issue18(self):
        formula = parse_file("tests/unittests/issue18.smt2",silent=False)
        oracle="""\
(declare-fun a () String)
(declare-fun b () String)
(assert (= a b))
(check-sat)
(assert (= a b))
(check-sat)"""
        self.assertEqual(oracle, formula.__str__())

    def test_issue25(self):
        script="""\
(declare-fun a () Bool)
(assert (= ((_ extract 5 3) (_ bv96 8))))
(check-sat)"""
        script = parse_str(script, silent=False)
        self.assertTrue("Term" in str(type(script.commands[1].term.subterms[0].subterms[0])))
        script="""\
(declare-fun bv () (_ BitVec 10))
(declare-fun a () Bool)
(assert (not (and (= ((_ extract 5 3) (_ bv96 8)) ((_ extract 4 2) (concat (_ bv121 7)
((_ extract 0 0) bv)))) (= (concat (_ bv1 1) (ite a (_ bv0 1) (_ bv1 1))) ((_ extract 1 0)
(ite a (_ bv6 3) (_ bv3 3)))))))
(check-sat)"""
        script = parse_str(script, silent=False)
        self.assertTrue(script != None)

if __name__ == '__main__':
    unittest.main()

