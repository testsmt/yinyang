import unittest
import sys
sys.path.append("../../")

from src.parsing.ast import * 
from src.parsing.parse import *

class TermTestCase(unittest.TestCase): 
    def test_term(self): 
        formula1="""
                (declare-const y Int)
                (declare-const v Bool)
                (assert (= v (not (= y (- 1)))))
                (assert (ite v false (= y (- 1))))
                (check-sat)
        """
        formula2="""
                (declare-const x Int)
                (declare-const y Int)
                (assert (= (+ x y) y))
        """

     

        def var2const():
            script=parse_str(formula1)
            script.commands[2].term.substitute(
                    Var(name="v",type="Bool"), 
                    Const(name="true",type="Bool")
            )
            self.assertEqual(
                    script.commands[2].term.__str__(),
                    "(= true (not (= y (- 1))))"
            ) 
        
        def entire_expr():
            assert_expr = parse_str(formula2).commands[2].term
            z = Var("z","Int")
            y = Var("y","Int")
            assert_expr.substitute(assert_expr, Expr("-",[z,y]))
            self.assertEqual(assert_expr.__str__(), "(- z y)")

        def subexpr():
            z = Var("z","Int")
            y = Var("y","Int")
            assert_expr = parse_str(formula2).commands[2].term
            assert_expr.substitute(assert_expr.subterms[0], Expr("-",[z,y]))
            self.assertEqual(assert_expr.__str__(), "(= (- z y) y)")

        def substitute_all():
            formula=\
            """
            (declare-const x String)
            (declare-const y String)
            (declare-const z String)
            (declare-const c String)
            (assert (= x (str.substr z 0 (str.len x))))
            """
            expr = parse_str(formula).commands[4].term
            x = Var("x","String")
            var1 = Var("var1","String")
            expr.substitute_all(x,var1)
            self.assertEqual(expr.__str__(),"(= var1 (str.substr z 0 (str.len var1)))")

        var2const()
        entire_expr()
        subexpr()
        substitute_all()

        
if __name__ == '__main__':
    # unittest.main()
    TermTestCase().test_term()
