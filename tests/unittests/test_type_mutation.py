import unittest
import sys
sys.path.append("../../")
import os

from src.parsing.parse import *
from src.parsing.typechecker import Context, typecheck
from src.parsing.typechecker_recur import typecheck_recur
from src.generators.TypeAwareOpMutation import TypeAwareOpMutation
from src.generators.TypeMutation import *

class Mockargs:
    name = ""
    modulo = 3

N = 500

class TypeAwareMutationTestCase(unittest.TestCase):
    def test_ta(self):
        formulafile="formula.smt2"
        formula = """
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (> (* (+ 3 x) (- y 2)) (div 5 z)))
        (assert (= (+ 7 y) x))
        (assert (< 6 (div (+ 4 x) z)))
        (check-sat)
        """
        with open(formulafile,"w") as f: 
            f.write(formula)
        script, glob = parse_str(formula)
        typecheck(script, glob)
        args = Mockargs()
        args.name = formulafile.strip(".smt2")
        script, glob = parse_file(formulafile,silent=True)
        typecheck(script, glob)
        av_expr = []
        expr_type = []
        for i in range(len(script.assert_cmd)):
            exps, typ = typecheck_recur(script.assert_cmd[i]) 
            av_expr += exps
            expr_type += typ
        unique_expr = [[],[],[],[],[],[]]
        for i in range(len(expr_type)):
            if expr_type[i] == BOOLEAN_TYPE:
                unique_expr[0].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == REAL_TYPE:
                unique_expr[1].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == INTEGER_TYPE:
                unique_expr[2].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == ROUNDINGMODE_TYPE:
                unique_expr[3].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == STRING_TYPE:
                unique_expr[4].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == REGEXP_TYPE:
                unique_expr[5].append(copy.deepcopy(av_expr[i]))
        for i in range(6):
            if unique_expr[i]:
                for j in range(len(unique_expr[i])-1):
                    for k in range(len(unique_expr[i])-j-1):
                        if unique_expr[i][len(unique_expr[i])-j-1] == unique_expr[i][k]:
                            del unique_expr[i][len(unique_expr[i])-j-1]
        gen = TypeMutation(script,args,unique_expr)
        gen.generate()
        os.system("rm "+formulafile)

    def test_mutation(self):
        formulafile="formula.smt2"
        formula = """
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Real)
        (declare-const e Real)
        (assert (> a (+ b 2)))
        (assert (= a (+ (* 2 c) 10)))
        (assert (<= (+ c b) 1000))
        (assert (>= d e))
        (check-sat)
        (get-model)
        """
        possible_outcome = ["(assert (> c (+ b 2)))",
                            "(assert (= b (+ (* 2 c) 10)))",
                            "(assert (<= (+ c a) 1000))"                          
                            ]
        with open(formulafile,"w") as f: 
            f.write(formula)
        args = Mockargs()
        print(formulafile)
        args.name = formulafile.strip(".smt2")
        script, glob = parse_file(formulafile,silent=True)
        typecheck(script, glob)
        av_expr = []
        expr_type = []
        for i in range(len(script.assert_cmd)):
            exps, typ = typecheck_recur(script.assert_cmd[i]) 
            av_expr += exps
            expr_type += typ
        unique_expr = [[],[],[],[],[],[]]
        for i in range(len(expr_type)):
            if expr_type[i] == BOOLEAN_TYPE:
                unique_expr[0].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == REAL_TYPE:
                unique_expr[1].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == INTEGER_TYPE:
                unique_expr[2].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == ROUNDINGMODE_TYPE:
                unique_expr[3].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == STRING_TYPE:
                unique_expr[4].append(copy.deepcopy(av_expr[i]))
            elif expr_type[i] == REGEXP_TYPE:
                unique_expr[5].append(copy.deepcopy(av_expr[i]))
        for i in range(6):
            if unique_expr[i]:
                for j in range(len(unique_expr[i])-1):
                    for k in range(len(unique_expr[i])-j-1):
                        if unique_expr[i][len(unique_expr[i])-j-1] == unique_expr[i][k]:
                            del unique_expr[i][len(unique_expr[i])-j-1]
        for i in range(N):
            script, glob = parse_file(formulafile,silent=True)
            typecheck(script, glob)
            gen = TypeMutation(script,args,unique_expr)
            gen.generate()
            for cmd in gen.formula.assert_cmd:
                if str(cmd) in possible_outcome:
                    possible_outcome.remove(str(cmd))
            if not possible_outcome:
                os.system("rm "+formulafile)
                print("true")
                return True
        os.system("rm "+formulafile)
        return False


if __name__ == '__main__':
    unittest.main()

