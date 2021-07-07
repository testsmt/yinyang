from src.parsing.Types import *

class Operator:
    def __init__(self,name,types,attributes,parameters=[]):
        self.name = name
        self.arg_types = [sort2type(t) for t in types[:-1]]
        self.rtype = sort2type(types[-1])
        self.attributes = attributes

    def __str__(self):
        s = self.name + ":"+ ",".join(self.arg_types) + " -> " + self.rtype
        if self.attributes != []:
            s+= " " + " ".join(self.attributes)
        return s

    def __repr__(self):
        return self.__str__()

def handle_non_parametric_op(tokens):
    op_name, type_strings, attributes = "", [],[]
    for idx,tok in enumerate(tokens):
        if tok == "": continue # ignore empty token
        if idx == 0: # first token is the operator name
            op_name = tok[1:]
        elif ":" != tok[0]:
            type_strings.append(tok.strip(")"))
        else:
            attributes.append(tok.strip(")"))
    return op_name, type_strings, attributes

def handle_parametric_op(tokens):
    op_name, type_strings, attributes, parameters = "", [],[],[]
    for idx,tok in enumerate(tokens):
        if idx == 0: continue
        if idx == 1:
            parameters.append(tok.strip("(").strip(")"))
            continue
        if idx == 2:
            op_name = tok[1:]
        elif ":" != tok[0]:
            type_strings.append(tok.strip(")"))
        else:
            attributes.append(tok.strip(")"))
    return op_name, type_strings, attributes, parameters
