import random

from src.generators.Generator import Generator

class TypeAwareOpMutation(Generator): 

    op2type = {
        "(=": "T T Bool",
        "(distinct": "T T Bool",
        "(<=": "Num Num Bool",
        "(>=": "Num Num Bool",
        "(<": "Num Num Bool",
        "(>": "Num Num Bool",
        "(+" : "Num Num Num",
        "(/" : "Real Real Real",
        "(-" : "Num Num Num",
        "(*" : "Num Num Num",
        "(div": "Int Int Int",
        "(mod": "Int Int Int",
        "(not" : "Bool Bool",
        "(and" : "Bool Bool Bool",
        "(or" : "Bool Bool Bool",
        "(forall": "Q",
        "(exists": "Q",
    }

    def __init__(self, seeds, args): 
        super().__init__(seeds)
        assert(len(seeds) == 1)
        self.type2ops = {}
        for k,v in self.op2type.items():
            if not v in self.type2ops: self.type2ops[v] = [k]
            else: self.type2ops[v].append(k)
        self.args = args
        self.fn = seeds[0]

    def tokenize(self, fn):
        with open(fn) as f:
            lines = []
            for line in f.readlines():
                if "(set-info :status" in line: line = ";" + line
                lines.append(line)
            return "".join(lines).split(" ")
        return None
    
    def toks2formula(self, toks):
        return " ".join(toks)

    def mutate(self, toks):
        new_toks = []
        r = random.randint(0,len(toks))
        for i, tok in enumerate(toks[r:]):
            op_type = None
            if tok in self.op2type:
                if tok == "(not":
                    toks[r+i] = random.choice(["(and","(or"])
                    return toks
                op_type = self.op2type[tok]
                ops = self.type2ops[op_type].copy()
                ops.remove(tok)
                if len(ops) == 0:
                    # Fallback case that should not happen if op2type
                    # is correctly defined
                    return self.mutate(toks)
                toks[r+i] = random.choice(ops)
                if tok == "(-": toks.insert(r+i+1, str(random.randint(1, 1000)))
                if tok == "(not": toks.insert(r+i+1, "false")
                break
        return toks
     
    def generate(self):
        toks = self.tokenize(self.fn)
        mutated_toks = self.mutate(toks)
        mutated_formula = self.toks2formula(mutated_toks)
        mutated_fn = "%s/%s.smt2" % (self.args.scratchfolder, self.args.name)
        with open(mutated_fn,"w") as f: f.write(mutated_formula)
        return mutated_fn
