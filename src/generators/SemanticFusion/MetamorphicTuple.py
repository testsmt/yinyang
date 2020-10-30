import random
import copy
import string

from src.parsing.ast import *

def gen_random_string(length):
    letters = string.ascii_lowercase
    return ''.join(random.choice(letters) for i in range(length))

class MetamorphicTuple:
    def __init__(self, template, x, y):
        self.template = copy.deepcopy(template)
        self.x = x
        self.y = y
        self.z = Var(self.x.name +"_"+self.y.name+"_fused",self.x.type)
        self.c = None
        new_cmds = []

        for v in template.free_var_occs:
            if v.name == "c":
                self.c = v
                break

        for cmd in template.commands:
            if isinstance(cmd,DeclareConst):
               if cmd.symbol == "c":
                    continue
            new_cmds.append(cmd)

        self.template.commands = new_cmds
        for i, cmd in enumerate(self.template.commands):
            if isinstance(cmd, Assert):
                break
        if self.c:
            self.c_type = self.x.type

        for ass in self.template.commands[i:]:
            ass.term.substitute_all(Var("x",self.x.type),x)
            ass.term.substitute_all(Var("y",self.y.type),y)
            ass.term.substitute_all(Var("z",self.z.type),self.z)
            if self.c:
                ass.term.substitute_all(Var("c", self.z.type), self.c_substituent())

    def x_substituent(self):
        cmds = self.template.commands
        return cmds[4].term.subterms[1]

    def y_substituent(self):
        cmds = self.template.commands
        return cmds[5].term.subterms[1]

    def c_substituent(self):
        if self.c_type == "Int":
            r = random.randint(-1000,1000)
            if r < 0:
                return Expr(op="-", subterms=[Const(name=str(-r), type=self.c_type)])
            else:
                return Const(name=str(), type=self.c_type)
        if self.x.type == "Real":
            r = round(random.uniform(-1000, 1000),5)
            if r < 0:
                return Expr(op="-", subterms=[Const(name=str(-r), type=self.c_type)])
            else:
                return Const(str(r), type=self.c_type)
        if self.x.type == "Bool":
            return Const(random.choice(["true","false"]),type=self.c_type)
        if self.x.type == "String":
            length = random.randint(0, 20)
            return Const('"'+gen_random_string(length)+'"',type=self.c_type)

    def xyz_constraints(self):
        return self.template.commands[3:6]

    def __str__(self):
        return "(" + self.x.__str__() + "," +  self.y.__str__() + ")"
