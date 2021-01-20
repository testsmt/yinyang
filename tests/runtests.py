import sys

import unittest
sys.path.append("../")

from tests.unittests.test_type_aware_op_mutation import TypeAwareOpMutationTestCase
from tests.unittests.test_semantic_fusion import SemanticFusionTestCase
from tests.unittests.test_term import TermTestCase
# TODO: re-enable these tests  
# from tests.unittests.test_typechecker import TypecheckerTestCase
from tests.unittests.test_type_mutation import TypeAwareMutationTestCase

if __name__ == '__main__':
    unittest.main()
