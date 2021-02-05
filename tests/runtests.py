import sys

import unittest
sys.path.append("../")

from tests.unittests.test_type_aware_op_mutation import TypeAwareOpMutationTestCase
from tests.unittests.test_semantic_fusion import SemanticFusionTestCase
from tests.unittests.test_term import TermTestCase
from tests.unittests.test_type_mutation import TypeAwareMutationTestCase
from tests.unittests.test_typechecker import TypecheckerTestCase

if __name__ == '__main__':
    unittest.main()
