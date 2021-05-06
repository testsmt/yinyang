import unittest
import os
import sys
sys.path.append("../../")

from src.parsing.parse import *                                                    

class ParsingTestCase(unittest.TestCase):
    def test_issue9(self): 
        formula = parse_file("tests/unittests/issue7.smt2")
        return '\x0a' in formula.__str__() and '\n' in formula.__str__()
  

if __name__ == '__main__':
    unittest.main()

