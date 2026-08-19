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

import copy
import random
import string
import threading


def random_string(length=5):
    return "".join(random.sample(string.ascii_letters + string.digits, length))


def deepcopy_safe(obj, stack_size=256 * 1024 * 1024):
    """
    copy.deepcopy() recurses once per nested/linked object it visits, and
    each level of that recursion burns several C stack frames internally
    (_reconstruct -> deepcopy -> _deepcopy_dict/_deepcopy_list -> deepcopy
    -> ...). For a large or deeply nested AST, that can exceed the
    process's actual OS thread stack well before Python's own (very high,
    see sys.setrecursionlimit in Typechecker.py) recursion limit ever
    triggers a catchable RecursionError -- crashing the interpreter with a
    silent segfault instead. Run the deepcopy on a worker thread with a
    much larger stack to avoid that.
    """
    result = {}

    def _work():
        try:
            result["value"] = copy.deepcopy(obj)
        except BaseException as e:
            result["error"] = e

    old_stack_size = threading.stack_size()
    try:
        threading.stack_size(stack_size)
    except (ValueError, RuntimeError):
        pass
    try:
        t = threading.Thread(target=_work)
        t.start()
        t.join()
    finally:
        try:
            threading.stack_size(old_stack_size)
        except (ValueError, RuntimeError):
            pass

    if "error" in result:
        raise result["error"]
    return result["value"]


def plain(cli):
    plain_cli = ""
    for token in cli.split(" "):
        plain_cli += token.split("/")[-1]
    return escape(plain_cli)


def escape(s):
    s = s.replace(".", "")
    s = s.replace("=", "")
    return s


def in_list(stdout, stderr, lst):
    stdstream = stdout + " " + stderr
    for err in lst:
        if err in stdstream:
            return True
    return False
