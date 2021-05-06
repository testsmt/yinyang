import unittest
import os
import sys
sys.path.append("../../")

from src.parsing.parse import *                                                    

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
        

            

if __name__ == '__main__':
    unittest.main()

