import hashlib
import base64

from src.generators.SemanticFusion.MetamorphicRelation import MR

class Symbol:
    def __init__(self, name, type):
        self.name = name
        self.type = type
        self.occurrences = 0

    def set_occurrences(self, script):
        self.occurrences += script.count(" "+self.name+" ")
        self.occurrences += script.count("("+self.name+" ")
        self.occurrences += script.count(" "+self.name+")")
        return self.occurrences


class Symbols:
    symbols = []

    def __init__(self, symbols):
        self.symbols = []
        for symbol in symbols:
            self.symbols.append(symbol)

    def get_shiftmap(self, prefix):
        original = []
        shift = []
        for symbol in self.symbols:
            original.append(symbol.name)
            if "|" in symbol.name:
                shift.append("|"+ prefix + symbol.name.strip("|") + "|")
            else:
                shift.append(prefix + symbol.name)
        shiftmap = dict(zip(original, shift))
        return shiftmap

    def set_value(self, model):
        for assignment in model:
            for symbol in self.symbols:
                if symbol.name == assignment[0]:
                    symbol.value = assignment[1]

    def dump(self):
        for s in self.symbols:
            print("name:" + s.name + " " + "type:" + str(s.type))


class MetamorphicTuple:
    def __init__(self, first_var, second_var):
        self.first_var = first_var
        self.second_var = second_var

        assert first_var.type == second_var.type
        self.type = str(first_var.type)

        hash_code = hashlib.md5((first_var.name + second_var.name).encode("utf-8")).digest()
        unique_id = base64.urlsafe_b64encode(hash_code).decode("utf-8")
        unique_id = ''.join([i for i in unique_id if i != '-' and i != '_' and not i.isdigit()])[:7]
        self.new_var = Symbol(unique_id + "_new", self.type)

        self.mr = MR(self.first_var, self.second_var, self.new_var, self.type)

    def get_x_substituent(self):
        return self.mr.get_x_substituent()

    def get_y_substituent(self):
        return self.mr.get_y_substituent()

    def get_xy_constraints(self):
        return self.mr.get_xy_constraints()

    def get_z_declaration(self):
        #if "BV" in self.type:
       #     symbol_type = "(_ BitVec " + self.type.strip("BV{").strip("}") + ")"
#         if "Array" in self.type:
            # symbol_type = "%s" % (self.type)
        symbol_type = self.type
        z_declaration = "(declare-fun %s () %s)" % (self.new_var.name, symbol_type)
        return z_declaration