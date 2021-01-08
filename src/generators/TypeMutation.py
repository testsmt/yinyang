import random
import copy

from src.generators.Generator import Generator
from src.parsing.parse import *
from src.parsing.typechecker_recur import *

class TypeMutation(Generator):
    # currently only support the mutation within the expression
    # muatation between expressions to be implemented 
    def __init__(self, seed_fns, args, ctxt):
        assert(len(seed_fns) == 1)
        self.seed_fn = seed_fns[0]
        self.args = args 
        self.formula, _ = parse_file(seed_fns[0])
        self.ctxt = ctxt

    def get_replacee(self, av_expr, expr_type):
        # first, categorize expressions per type
        # 0: Bool, 1: Real, 2: Int, 3: RoundingMode, 4: String, 5: Regex
        exprs = [[],[],[],[],[],[]]
        for i in range(len(av_expr)):
            if expr_type[i] == BOOLEAN_TYPE:
                exprs[0].append(av_expr[i])
            elif expr_type[i] == REAL_TYPE:
                exprs[1].append(av_expr[i])
            elif expr_type[i] == INTEGER_TYPE:
                exprs[2].append(av_expr[i])
            elif expr_type[i] == ROUNDINGMODE_TYPE:
                exprs[3].append(av_expr[i])
            elif expr_type[i] == STRING_TYPE:
                exprs[4].append(av_expr[i])
            elif expr_type[i] == Regex:
                exprs[5].append(av_expr[i])
        types = [0,1,2,3,4,5]
        typ = random.choice(types)
        while len(exprs[typ]) < 2:
            types.remove(typ)
            typ = random.choice(types)
        t1, t2 = random.sample(exprs[typ],2)
        return t1, t2

    def _add_seedinfo(self,formula):
        formula.commands = [Comment(self.seed_fn)] + formula.commands

    def generate(self):
        cmd = random.choice(self.formula.assert_cmd)
        av_expr, expr_type = typecheck_recur_list(cmd, self.ctxt)
        t1, t2 = self.get_replacee(av_expr, expr_type)
        t1_copy = copy.deepcopy(t1)
        t2_copy = copy.deepcopy(t2)
        cmd.term.substitute(t1, t2_copy)
        cmd.term.substitute(t2, t1_copy)
        return self._add_seedinfo(self.formula), True