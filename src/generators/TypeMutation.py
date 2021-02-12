import random
import copy

from src.generators.Generator import Generator
from src.parsing.parse import *
from src.parsing.typechecker_recur import *

type2num = {'Bool': 0, 'Real': 1, 'Int': 2, 'RoundingMode': 3, 'String': 4, 
'RegLan': 5, 'Unknown': 6}

class TypeMutation(Generator):
    def __init__(self, formula, args):
        self.args = args 
        self.formula = formula 

    def categorize(self, av_expr, expr_type):
        # 0: Bool, 1: Real, 2: Int, 3: RoundingMode, 4: String, 5: Regex, 6: Unknown 
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
                for j in range(1, len(unique_expr[i])):
                    for k in range(j):
                        if unique_expr[i][len(unique_expr[i])-j] == unique_expr[i][k]:
                            unique_expr[i][len(unique_expr[i])-j]
        return unique_expr
        
    def get_replacee(self, av_expr, expr_type):
        unique_expr = self.categorize(av_expr, expr_type)
        pool = [i for i in range(len(av_expr))]
        counter = 0
        while counter <= 10:
            if pool:
                k = random.choice(pool)
                t1 = av_expr[k]
                typ = type2num[expr_type[k]]
                if unique_expr[typ]:
                    t2 = random.choice(unique_expr[typ])
                    if t1 != t2:
                        return t1, t2
                    else:
                        pool.remove(k)
                        counter += 1 
                else:
                    pool.remove(k)
                    counter += 1
            else:
                return False
        return False 

    def generate(self):
        av_expr = []
        expr_type = []
        for _ in range(self.args.modulo):
            for i in range(len(self.formula.assert_cmd)):
                exps, typ = typecheck_recur(self.formula.assert_cmd[i]) 
                av_expr += exps
                expr_type += typ
            res = self.get_replacee(av_expr,expr_type)
            if res:
                t1, t2 = res
                t1.substitute(t1, t2)
                return self.formula, True      
        return None, False
