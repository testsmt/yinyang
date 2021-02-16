import random
import copy

from src.generators.Generator import Generator
from src.parsing.parse import *
from src.parsing.typechecker_recur import *

type2num = {'Bool': 0, 'Real': 1, 'Int': 2, 'RoundingMode': 3, 'String': 4, 
'RegLan': 5, 'Unknown': 6}

class TypeMutation(Generator):
    def __init__(self, formula, args, unique_expr):
        self.args = args 
        self.formula = formula 
        self.unique_expr = unique_expr
        self.av_expr = []
        self.expr_type = []
        
    def get_replacee(self):
        self.av_expr = []
        self.expr_type = []
        for i in range(len(self.formula.assert_cmd)):
            exps, typ = typecheck_recur(self.formula.assert_cmd[i]) 
            self.av_expr += exps
            self.expr_type += typ
        pool = [i for i in range(len(self.av_expr))]
        counter = 0
        while counter <= 5:
            if pool:
                k = random.choice(pool)
                t1 = self.av_expr[k]
                typ = type2num[self.expr_type[k]]
                if self.unique_expr[typ]:
                    t2 = random.choice(self.unique_expr[typ])
                    if t1 == t2:
                        pool.remove(k)
                        counter += 1 
                    else:
                        return t1, t2
                else:
                    pool.remove(k)
                    counter += 1
            else:
                return False
        return False 

    def generate(self):
        for _ in range(self.args.modulo):
            res = self.get_replacee()
            if res:
                t1, t2 = res
                print("{} -> {}".format(t1,t2))
                t1.substitute(t1, t2)
                print(self.formula)
                return self.formula, True      
        return None, False
