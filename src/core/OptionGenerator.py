# MIT License
#
# Copyright (c) [2020 - 2020] The yinyang authors
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


# This file is about option fuzzer support.
# OptionGenerator reads a options setting file to generate a random option
# configuration for the corresponding solvers.
# The format of the options setting file is as follow:

# ```
# <solver keywords>
# <option name> [type|value]*
# <option name> [type|value]*
# ###
# <solver keywords>
# <option name> [type|value]*
# <option name> [type|value]*
# ###
# <solver keywords>
# <option name> [type|value]*
# <option name> [type|value]*
# ```

# `<solver keywords>`: Keywords for the solver command-line interfaces.
#                      If the keywords are found in the command-line interfaces
#                      yinyang will generate a corresponding random option
#                      setting.

# `<option name>`: Name of the option item.

# `[type|value]*`: Type or value of the option.
#                  The type can be either `bool` or `int`.
#                  The value can be either `true`,`false`, or an integer.
#                  In default, i.e., leaving this position empty, the option is
#                  assigned to `bool` type. Optfuzz will generate a random
#                  value according to the type of the option.

# `###`: Mark for splitting the option setting blocks.
#        The options in different blocks are independent.


import random

from enum import Enum


class OptionType(Enum):
    BOOL = 0
    INT = 1


class Option:
    def __init__(self, name, type, min=0, max=1000):
        self.name = name
        self.type = type
        self.min = min
        self.max = max


class ConfigBlock:
    def __init__(self):
        self.cmd = ""
        self.optionList = []


class OptionGenerator:
    def __init__(self, fn):
        with open(fn, "r") as reader:
            text = reader.read()
        self.configBlocks = []
        self.parse(text)

    def generate(self, cli):
        ret = ""
        for block in self.configBlocks:
            if block.cmd in cli:
                for option in block.optionList:
                    if option.type == OptionType.BOOL:
                        if option.max == option.min:
                            if option.max == 0:
                                boolean = "false"
                            else:
                                boolean = "true"
                        else:
                            if bool(random.getrandbits(1)):
                                boolean = "true"
                            else:
                                boolean = "false"
                        ret += "(set-option :%s %s)\n" % (option.name, boolean)
                    elif option.type == OptionType.INT:
                        ret += "(set-option :%s %s)\n" % (
                            option.name,
                            str(random.randrange(option.min, option.max + 1)),
                        )
        return ret

    def parse(self, text):
        configBlocks = text.split("###")
        for item in configBlocks:
            configBlock = ConfigBlock()
            configs = item.split("\n")
            for config in configs:
                if config != "":
                    if configBlock.cmd == "":
                        configBlock.cmd = config
                        continue
                    config = config.strip(" ").split(" ")
                    if len(config) == 1:
                        configBlock.optionList.append(
                            Option(config[0], OptionType.BOOL)
                        )
                    elif len(config) == 2:
                        if config[1] == "bool":
                            configBlock.optionList.append(
                                Option(config[0], OptionType.BOOL)
                            )
                        elif config[1] == "true":
                            configBlock.optionList.append(
                                Option(config[0], OptionType.BOOL, 1, 1)
                            )
                        elif config[1] == "false":
                            configBlock.optionList.append(
                                Option(config[0], OptionType.BOOL, 0, 0)
                            )
                        elif config[1] == "int":
                            configBlock.optionList.append(
                                Option(config[0], OptionType.INT)
                            )
                        elif config[1].isdigit():
                            configBlock.optionList.append(
                                Option(
                                    config[0],
                                    OptionType.INT,
                                    int(config[1]),
                                    int(config[1]),
                                )
                            )
                        elif "-" in config[1]:
                            bound = config[1].split("-")
                            if (
                                len(bound) == 2
                                and bound[0].isdigit()
                                and bound[1].isdigit()
                                and int(bound[0]) <= int(bound[1])
                            ):
                                configBlock.optionList.append(
                                    Option(
                                        config[0],
                                        OptionType.INT,
                                        int(bound[0]),
                                        int(bound[1]),
                                    )
                                )
                            else:
                                exit(
                                    "error: The range of the config is not\
                                     valid (e.g. 1-10):"
                                    + config[1]
                                )
                        else:
                            exit(
                                "error: The argument setting of the config is\
                                not valid (e.g. proof true): "
                                + config[1]
                            )
                    else:
                        exit(
                            "error: The argument setting of the config is not\
                             valid (e.g. proof true):"
                            + config[1]
                        )
            self.configBlocks.append(configBlock)
