import random
import itertools
import string
import copy

from src.parsing.ast import *
from src.generators.SemanticFusion.VariableFusion import *

def cvars(occs): 
    """
    Return a single representative occurrence for each variable.  
    """
    names = []
    canonicals = [] 
    for occ in occs: 
        if occ.name in names:
            continue 
        canonicals.append(occ)
    return canonicals 


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

def type_var_map(global_vars):
    mapping = {} 
    for var in global_vars: 
        if global_vars[var] not in mapping: 
            mapping[global_vars[var]] = [var]
        else: 
            if not var in mapping[global_vars[var]]:
                mapping[global_vars[var]].append(var)
    return mapping 


# def random_tuple_list(lst1, lst2, lb=1):
    # """
    # Generate a random list of tuples (x,y) where x is in lst1 and y is in lst2  
    # """
    # len_lst1 = len(lst1) 
    # len_lst2 = len(lst2) 
    # k = random.randint(lb,max(len_lst1,len_lst2))
    # return random.sample(list(itertools.product(lst1,lst2)),k)


def random_tuple_list(lst1, lst2, lb=1):
    """
    Generate a random list of tuples (x,y) where x is in lst1 and y is in lst2;
    """
    len_lst1 = len(lst1)
    len_lst2 = len(lst2)

    product = list(itertools.product(lst1, lst2))

    if len(product) == 0:
        k = 0
    else:
        k = random.randint(lb, len(product))
    tups = random.sample(product,k)
    random.shuffle(tups)

    new_tups = []
    lhs, rhs = [], []
    for tup in tups:
        if tup[0] in lhs: continue
        if tup[1] in rhs: continue
        lhs.append(tup[0])
        rhs.append(tup[1])
        new_tups.append(tup)
    return new_tups

def create_var_map(m1, m2, templates): 
    """
    Create a random variable mapping of variables with same type      
    """
    mapping=[]
    for t in templates:
        if not t in m1: continue
        if not t in m2: continue
        random_tuples = random_tuple_list(m1[t],m2[t])
        for tup in random_tuples:
            mapping.append((tup[0], tup[1], random.choice(templates[t]), t))
    return mapping 


def random_var_triplets(global_vars1, global_vars2, templates):
    m1, m2 = type_var_map(global_vars1), type_var_map(global_vars2)
    # if var_map == []:
    #     return None
    # triplets = []
    # for v in var_map:
    #     template = v[2]
    #     var_occs1 = [var for var in global_vars1 if var == v[0]]
    #     var_occs2 = [var for var in global_vars2 if var == v[1]]
    #     random_occs = random_tuple_list(var_occs1, var_occs2)
    #     for occ in random_occs:
    #         triplets.append((occ[0], occ[1], template))
    return create_var_map(m1, m2, templates)  
