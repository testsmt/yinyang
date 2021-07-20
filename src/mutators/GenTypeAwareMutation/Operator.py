# MIT License
#
# Copyright (c) [2020 - 2021] The yinyang authors
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

from src.parsing.Types import sort2type


class Operator:
    def __init__(self, name, types, attributes, parameters=[]):
        self.name = name
        self.arg_types = [sort2type(t) for t in types[:-1]]
        self.rtype = sort2type(types[-1])
        self.attributes = attributes

    def __str__(self):
        s = self.name + ":" + ",".join(self.arg_types) + " -> " + self.rtype
        if self.attributes != []:
            s += " " + " ".join(self.attributes)
        return s

    def __repr__(self):
        return self.__str__()


def handle_non_parametric_op(tokens):
    op_name, type_strings, attributes = "", [], []
    for idx, tok in enumerate(tokens):
        if tok == "":
            continue  # ignore empty token
        if idx == 0:  # first token is the operator name
            op_name = tok[1:]
        elif ":" != tok[0]:
            type_strings.append(tok.strip(")"))
        else:
            attributes.append(tok.strip(")"))
    return op_name, type_strings, attributes


def handle_parametric_op(tokens):
    op_name, type_strings, attributes, parameters = "", [], [], []
    for idx, tok in enumerate(tokens):
        if idx == 0:
            continue
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
