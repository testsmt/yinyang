import random

from src.generators.Generator import Generator
from src.parsing.parse import *


class TypeAwareOpMutation(Generator):
    def __init__(self, seed_fns, args):
        assert(len(seed_fns) == 1)
        self.seed_fn = seed_fns[0]
        self.args = args
        self.formula = parse_file(seed_fns[0])
        self.bidirectional = []
        self.unidirectional = []

        self.parse_config_file()

    def parse_config_file(self):
        with open(self.args.opconfig) as f:
            lines = f.readlines()
        for l in lines:
            if ";" in l: continue
            if not l.strip(): continue
            arity = -1
            if ":arity" in l:
                arity = l.split(":arity")[-1].split(" ")[-1].strip()
                l =  " ".join(l.split(" ")[:-2])
            if "->" in l:
                op_from,op_to = l.split("->")[0].strip(), l.split("->")[1].strip()
                self.unidirectional.append((arity,op_from,op_to))
                continue

            op_class = [op.strip() for op in l.split(",")]
            self.bidirectional.append((arity, op_class))

    def arities_mismatch(self, arity, op_occ):
        if arity == "2+" and len(op_occ.subterms) < 2:
           return True

        if arity == "1-" and len(op_occ.subterms) > 2:
            return True
        return False

    def get_replacee(self,op_occ):
        for b in self.bidirectional:
            arity, op_class = b[0], b[1]
            if self.arities_mismatch(arity,op_occ):
                continue

            if op_occ.op in op_class:
                diff = op_class.copy()
                diff.remove(op_occ.op)
                replacee = random.choice(diff)
                return replacee

            if op_occ.quantifier in op_class:
                diff = op_class.copy()
                diff.remove(op_occ.quantifier)
                replacee = random.choice(diff)
                return replacee

        for u in self.unidirectional:
            arity, op, replacee = u[0], u[1], u[2]
            if op_occ.op != op or op_occ.quantifier != op: continue
            if self.arities_mismatch(arity, op_occ):
                continue
            return replacee
        return None

    def generate(self):
        for _ in range(self.args.modulo):
            max_choices = len(self.formula.op_occs)
            for _ in range(max_choices):
                op_occ = random.choice(self.formula.op_occs)
                replacee = self.get_replacee(op_occ)
                if replacee:
                    # print(op_occ.op,"->",replacee)
                    op_occ.op = replacee
                    break
        return self.formula, True
