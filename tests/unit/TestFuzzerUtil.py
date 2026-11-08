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

import random
import unittest

from yinyang.src.core.FuzzerUtil import get_permutation_generator


class FuzzerUtilTestCase(unittest.TestCase):
    def test_permutation_generator(self):
        # SemanticFusion fuses each ordered pair of seeds once (including a
        # seed with itself), and every seed is a first seed within the
        # first n pairs.
        random.seed(1)
        seeds = ["s%d.smt2" % i for i in range(7)]
        pairs = list(get_permutation_generator(seeds))
        self.assertEqual(len(pairs), 7 * 7)
        self.assertEqual(set(pairs), {(a, b) for a in seeds for b in seeds})
        for r in range(7):
            round_pairs = pairs[7 * r:7 * (r + 1)]
            self.assertEqual({a for a, _ in round_pairs}, set(seeds))
            self.assertEqual({b for _, b in round_pairs}, set(seeds))
        self.assertEqual(set(get_permutation_generator(["a", "b"])),
                         {("a", "a"), ("a", "b"), ("b", "a"), ("b", "b")})


if __name__ == "__main__":
    unittest.main()
