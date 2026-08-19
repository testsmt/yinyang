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

import unittest
import sys

sys.path.append("../../")

from yinyang.src.base.Utils import deepcopy_safe


class Node:
    def __init__(self, v, children=None):
        self.v = v
        self.children = children or []


class UtilsTestCase(unittest.TestCase):
    def test_deepcopy_safe_produces_independent_copy(self):
        root = Node(1, [Node(2), Node(3, [Node(4)])])
        cp = deepcopy_safe(root)
        self.assertIsNot(cp, root)
        self.assertEqual(cp.v, 1)
        self.assertEqual(cp.children[1].children[0].v, 4)

        # mutating the copy must not affect the original (i.e. it's a
        # real deep copy, not a shallow/shared reference).
        cp.children[1].children[0].v = 999
        self.assertEqual(root.children[1].children[0].v, 4)

    def test_deepcopy_safe_propagates_exceptions(self):
        class Boom:
            def __deepcopy__(self, memo):
                raise ValueError("boom")

        with self.assertRaises(ValueError):
            deepcopy_safe(Boom())


if __name__ == "__main__":
    unittest.main()
