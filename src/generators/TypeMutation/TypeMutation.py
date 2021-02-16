import random
import copy

from src.generators.Generator import Generator
from src.parsing.parse import *
from src.generators.TypeMutation.util import * 


class TypeMutation(Generator):
    def __init__(self, formula, args, unique_expr):
        self.args = args 
        self.formula = formula 
        self.unique_expr = unique_expr

        
    def get_replacee(self):
        pool = [i for i in range(len(self.av_expr))]
        counter = 0
        while counter <= 5:
            if pool:
                k = random.choice(pool)
                t1 = self.av_expr[k]
                typ = type2num[self.expr_type[k]]
                if self.unique_expr[typ]:
                    t2 = random.choice(self.unique_expr[typ])
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
        self.av_expr, self.expr_type = get_all_subterms(self.formula)
        res = self.get_replacee()
        if res:
            t1, t2 = res
            print("change:",t1,"->", t2)
            print("av_expr",self.av_expr)
            print("unique_expr", self.unique_expr)
            if t1.type == BOOLEAN_TYPE: 
                print("-------------HERE--------------------------------")
            print("seed")
            print(self.formula)
            print("t1 before",t1)
            t1.substitute(t1, t2)
            print("t1 after", t2) 
            print()
            print("mutant")
            print(self.formula)
            return self.formula, True      
        return None, False
