import random
import string

metamorphic_relation_dictionary = {
    "Int":{
        "z = x * y",
        "z = x + y",
        "z = x + const + y"
    },
    "LinearInt":{
        "z = x + y",
        "z = x + const + y"
    },
    "Real":{
        "z = x * y",
        "z = x + y",
        "z = x + const + y",
        "z = const1 * x + const2 * y + const3"
    },
    "LinearReal":{
        "z = x + y",
        "z = x + const + y"
        "z = const1 * x + const2 * y + const3"
    },
    "Bool":{
        "z = x xor y"
    },
    "BV":{
        "z = x bvxor y"
    },
    "String":{
        "z = x str.++ y 1",
        "z = x str.++ y 2",
        "z = x str.++ y 3",
        "z = x str.++ const str.++ y"
    },
    "Array":{
        "z = (store (store _ 1 (store a 1 (select b 1))) 2 (store b 1 (select a 1)))"
    }
}
class MR:
    def __init__(self, x, y, z, var_type):
        self.x = x.name
        self.y = y.name
        self.z = z.name
        self.type = var_type

        if "BitVec" in self.type:
            self.mr = random.choice(list(metamorphic_relation_dictionary["BV"]))
        elif "Array" in self.type:
            self.mr = random.choice(list(metamorphic_relation_dictionary["Array"]))
        elif self.type in metamorphic_relation_dictionary:
            # if args.linear and ("Int" in self.type or "Real" in self.type):
            #     self.mr = random.choice(list(metamorphic_relation_dictionary["Linear"+self.type]))
            # else:
            self.mr = random.choice(list(metamorphic_relation_dictionary[self.type]))
        else: self.mr = None

        self.random_strings = []
        self.random_ints = []
        self.random_reals = []

        self.random_string = ''.join(random.sample(string.ascii_letters + string.digits, 5))



    def _get_string_const(self,id):
        if len(self.random_strings) < id:
            while len(self.random_strings) < id:
                self.random_strings.append(''.join(random.sample(string.ascii_letters + string.digits, 5)))
        return self.random_strings[id-1]

    def _get_int_const(self,id):
        if len(self.random_ints) < id:
            while len(self.random_ints) < id:
                random_int = round(random.randint(-1000,1000), 10)
                if random_int > 0: random_int_string = str(random_int)
                elif random_int < 0: random_int_string = "(- %s)" %(str(-random_int))
                else: random_int_string = "1"
                self.random_ints.append(random_int_string)
        return self.random_ints[id-1]

    def _get_real_const(self,id):
        if len(self.random_reals) < id:
            while len(self.random_reals) < id:
                random_real = random.uniform(-1000,1000)
                if random_real > 0: random_real_string = str(random_real)
                elif random_real < 0: random_real_string = "(- %s)" %(str(-random_real))
                else: random_real_string = "1.0"
                self.random_reals.append(random_real_string)
        return self.random_reals[id-1]

    def get_x_substituent(self):
        """ Retrive the substitution for x -> z op^-1 y """
        if self.type == "Int":
            if self.mr == "z = x * y":
                return "(div %s %s)" %(self.z, self.y)
            elif self.mr == "z = x + y":
                return "(- %s %s)" %(self.z, self.y)
            elif self.mr == "z = x + const + y":
                return "(- (- %s %s) %s)" %(self.z, self._get_int_const(1), self.y)

        elif self.type == "Real":
            if self.mr == "z = x * y":
                return "(/ %s %s)" %(self.z, self.y)
            elif self.mr == "z = x + y":
                return "(- %s %s)" %(self.z, self.y)
            elif self.mr == "z = x + const + y":
                return "(- (- %s %s) %s)" %(self.z, self._get_real_const(1), self.y)
            elif self.mr == "z = const1 * x + const2 * y + const3":
                return "(/ (- (- %s %s) (* %s %s)) %s)" %(self.z,
                                                          self._get_real_const(3),
                                                          self._get_real_const(2),
                                                          self.y,
                                                          self._get_real_const(1))

        elif self.type == "Bool":
            if self.mr == "z = x xor y":
                return "(xor %s %s)" %(self.z, self.y)

        elif "BV" in self.type:
            if self.mr == "z = x bvxor y":
                return "(bvxor %s %s)" %(self.z, self.y)

        elif self.type == "String":
            if self.mr == "z = x str.++ y 1":
                return "(str.substr %s 0 (str.len %s))" %(self.z, self.x)
            elif self.mr == "z = x str.++ y 2":
                return "(str.substr %s 0 (str.len %s))" %(self.z, self.x)
            elif self.mr == "z = x str.++ y 3":
                return "(str.substr %s 0 (str.len %s))" %(self.z, self.x)
            elif self.mr == "z = x str.++ const str.++ y":
                return "(str.substr %s 0 (str.len %s))" %(self.z, self.x)

        elif self.type == "Array":
            if self.mr == "z = (store (store _ 1 (store a 1 (select b 1))) 2 (store b 1 (select a 1)))":
                return "(store (select %s 1) 1 (select (select %s 2) 1))" %(self.z, self.z)

        return self.x


    def get_y_substituent(self):
        """ Retrive the substitution for y -> z op^-1 x """
        if self.type == "Int":
            if self.mr == "z = x * y":
                return "(div %s %s)" %(self.z, self.x)
            elif self.mr == "z = x + y":
                return "(- %s %s)" %(self.z, self.x)
            elif self.mr == "z = x + const + y":
                return "(- (- %s %s) %s)" %(self.z, self._get_int_const(1), self.x)

        elif self.type == "Real":
            if self.mr == "z = x * y":
                return "(/ %s %s)" %(self.z, self.x)
            elif self.mr == "z = x + y":
                return "(- %s %s)" %(self.z, self.x)
            elif self.mr == "z = x + const + y":
                return "(- (- %s %s) %s)" %(self.z, self._get_real_const(1), self.x)
            elif self.mr == "z = const1 * x + const2 * y + const3":
                return "(/ (- (- %s %s) (* %s %s)) %s)" \
                       %(self.z, self._get_real_const(3), self._get_real_const(1),
                         self.x, self._get_real_const(2))

        elif self.type == "Bool":
            if self.mr == "z = x xor y":
                return "(xor %s %s)" %(self.z, self.x)

        elif "BV" in self.type:
            if self.mr == "z = x bvxor y":
                return "(bvxor %s %s)" %(self.z, self.x)

        elif self.type == "String":
            if self.mr == "z = x str.++ y 1":
                return "(str.substr %s (str.len %s) (str.len %s))" %(self.z, self.x, self.y)
            elif self.mr == "z = x str.++ y 2":
                return '(str.replace %s %s (str.at %s (str.len %s)))' %(self.z, self.x, self.z, self.z)
            elif self.mr == "z = x str.++ y 3":
                return "(str.substr %s (str.len %s) (str.len %s))" %(self.z, self.x, self.y)
            elif self.mr == "z = x str.++ const str.++ y":
                return '(str.replace (str.replace %s %s (str.at %s (str.len %s))) "%s" (str.at %s (str.len %s)))' %(self.z, self.x, self.z, self.z, self._get_string_const(1), self.z, self.z)

        elif self.type == "Array":
            if self.mr == "z = (store (store _ 1 (store a 1 (select b 1))) 2 (store b 1 (select a 1)))":
                return "(store (select %s 2) 1 (select (select %s 1) 1))"  %(self.z, self.z)

        return self.y

    def get_xy_constraints(self):
        """ Return the constraints on x and y for unsat fusion """
        if self.type == "Int":
            if self.mr == "z = x * y":
                return "(assert (= %s (* %s %s)))" % (self.z, self.x, self.y) +\
                       "(assert (= %s (div %s %s)))" % (self.x, self.z, self.y) +\
                       "(assert (= %s (div %s %s)))" % (self.y, self.z, self.x)
            elif self.mr == "z = x + y":
                return "(assert (= %s (+ %s %s)))" %(self.z, self.x, self.y)
            elif self.mr == "z = x + const + y":
                return "(assert (= %s (+ (+ %s %s) %s)))" \
                       %(self.z, self.y, self.x, self._get_int_const(1))

        elif self.type == "Real":
            if self.mr == "z = x * y":
                return "(assert (= %s (* %s %s)))" % (self.z, self.x, self.y) +\
                       "(assert (= %s (/ %s %s)))" % (self.x, self.z, self.y) +\
                       "(assert (= %s (/ %s %s)))" % (self.y, self.z, self.x)
            elif self.mr == "z = x + y":
                return "(assert (= %s (+ %s %s)))" %(self.z, self.x, self.y)
            elif self.mr == "z = x + const + y":
                return "(assert (= %s (+ (+ %s %s) %s)))" \
                       %(self.z, self.y, self.x, self._get_real_const(1))
            elif self.mr == "z = const1 * x + const2 * y + const3":
                return "(assert (= %s (+ (+ (* %s %s) (* %s %s)) %s)))" \
                       %(self.z, self._get_real_const(1), self.x,
                         self._get_real_const(2), self.y, self._get_real_const(3))

        elif self.type == "Bool":
            if self.mr == "z = x xor y":
                return "(assert (= %s (xor %s %s)))" %(self.z, self.x, self.y)

        elif "BV" in self.type:
            if self.mr == "z = x bvxor y":
                return "(assert (= %s (bvxor %s %s)))" %(self.z, self.x, self.y)

        elif self.type == "String":
            if self.mr == "z = x str.++ y 1":
                return "(assert (= %s (str.++ %s %s)))" %(self.z, self.x, self.y)
            elif self.mr == "z = x str.++ y 2":
                return "(assert (= %s (str.++ %s %s)))" %(self.z, self.x, self.y)
            elif self.mr == "z = x str.++ y 3":
                return "(assert (= true (str.in.re %s (re.++ (str.to.re %s) (str.to.re %s)))))" %(self.z, self.x, self.y)
            elif self.mr == "z = x str.++ const str.++ y":
                return '(assert (= %s (str.++ (str.++ %s "%s") %s)))' \
                       %(self.z, self.x, self._get_string_const(1), self.y)

        elif self.type == "Array":
            if self.mr == "z = (store (store _ 1 (store a 1 (select b 1))) 2 (store b 1 (select a 1)))":
                return ""

        return ""
