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
        self.r = None

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
            if self.c.type == "Int": self.r = random.randint(-1000,1000)
            if self.c.type == "Real": self.r = round(random.uniform(-1000, 1000),1)
            if self.c.type == "Bool": self.r = random.choice(["true","false"])
            if self.c.type == "String": self.r = '"'+gen_random_string(length)+'"'

        for ass in self.template.commands[i:]:
            ass.term.substitute_all(Var("x",self.x.type),x)
            ass.term.substitute_all(Var("y",self.y.type),y)
            ass.term.substitute_all(Var("z",self.z.type),self.z)
            if self.c:
                print("self.c_substituent", self.c_substituent())
                print("c.name",self.c.name)
                ass.term.substitute_all(Var("c", self.z.type), self.c_substituent())
                
   
    def x_substituent(self):
        cmds = self.template.commands
        return cmds[4].term.subterms[1]

    def y_substituent(self):
        cmds = self.template.commands
        return cmds[5].term.subterms[1]

    def c_substituent(self):
        if self.c.type == "Int":
            if self.r < 0:
                return Expr(op="-", subterms=[Const(name=str(-self.r), type=self.c.type)])
            else:
                return Const(name=str(self.r), type=self.c.type)
        if self.c.type == "Real":
            if self.r < 0:
                return Expr(op="-", subterms=[Const(name=str(-self.r), type=self.c.type)])
            else:
                return Const(str(self.r), type=self.c.type)
        if self.c.type == "Bool":
            return Const(self.r,type=self.c.type)
        if self.c.type == "String":
            length = random.randint(0, 20)
            return Const(self.r,type=self.c.type)
        print("llllllllllllllllllllllllllllllllllllllllllllllllllllll",self.c.type, flush=True)

    def xyz_constraints(self):
        return self.template.commands[3:6]

    def __str__(self):
        return "(" + self.x.__str__() + "," +  self.y.__str__() + ")"
