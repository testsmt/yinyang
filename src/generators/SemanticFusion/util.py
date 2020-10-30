import random
import string
import copy

from src.generators.SemanticFusion.MetamorphicTuple import *


def debug_formula(formula,name="formula"):
    print("#"*10, name, "#"*10)
    print(formula.__str__())
    print("#"*(10+len(name)+10))
    print()


def is_constant(cmd):
    if isinstance(cmd,DeclareConst): return True
    if isinstance(cmd,DeclareFun) and cmd.input_sort == "": return True
    return False

def is_sort(cmd):
    if isinstance(cmd,SMTLIBCommand) and "-sort" in cmd.cmd_str:
        return True
    return False

def concat(op, script1, script2):
    script1.merge_asserts()
    script2.merge_asserts()
    sorts=[]
    cmd_str=[]
    sorts = [cmd for cmd in script1.commands + script2.commands if is_sort(cmd)]
    sorts = list(set(sorts))
    declares1 = [cmd for cmd in script1.commands if is_constant(cmd)]
    assert1 = [cmd for cmd in script1.commands if isinstance(cmd,Assert)][0]
    assert2 = [cmd for cmd in script2.commands if isinstance(cmd,Assert)][0]
    conjunction = Assert(Term(op=op,subterms=[assert1.term,assert2.term]))
    new_cmds = declares1

    for cmd in script2.commands:
        if is_sort(cmd):
            continue
        if isinstance(cmd,Assert):
            new_cmds.append(conjunction)
        else:
            new_cmds.append(cmd)
    new_cmds = sorts + new_cmds
    return Script(new_cmds, {**script1.global_vars, **script2.global_vars})

def conjunction(script1, script2):
    return concat("and", script1, script2)

def disjunction(script1, script2):
    return concat("or", script1, script2)

def random_mr_tuples(occs1,occs2,templates):
    supported_types = list(templates.keys())
    types2 = {occ2.type for occ2 in occs2}
    metamorphic_tuples = []
    for occ1 in occs1:
        if occ1.type not in types2: continue
        if occ1.type not in supported_types: continue
        occ2 = random.choice(occs2)
        while occ1.type != occ2.type:
            occ2 = random.choice(occs2)
        mr_template = random.choice(templates[occ1.type])
        metamorphic_tuples.append(MetamorphicTuple(mr_template, occ1, occ2))
    return metamorphic_tuples

def add_fusion_constraints(formula,asserts):
    i = -1
    for i,cmd in enumerate(formula.commands):
        if isinstance(cmd, CheckSat): break
    if i == -1: return
    formula.commands = formula.commands[:i] + asserts +  formula.commands[i:]

def add_var_decls(formula, vars):
    i = -1
    for cmd in formula.commands:
        if isinstance(cmd, Assert): break
        i += 1
    if i == -1: return
    var_decls =[]
    for var in vars:
        var_decls.append(DeclareConst(var.name,var.type))
    formula.commands = formula.commands[:i+1] + var_decls + formula.commands[i+1:]
