import unittest
import sys
sys.path.append("../..")

from src.modules.Solver import Solver, SolverResult, SolverResultType

class SolverTestCase(unittest.TestCase):
    def setUp(self):
        self.normalSolver = Solver("echo")
        self.sleepSolver = Solver("echo sat && sleep 5")

    def testsat(self):
        normalsat = "sat"
        result, _ = self.normalSolver.solve(normalsat,8)
        self.assertTrue(result.equals(SolverResultType.SAT))
        normalsat = """
sat
        """
        result, _ = self.normalSolver.solve(normalsat,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.SAT)))
        normalsat = """(some text)
sat
(some text)
        """
        result, _ = self.normalSolver.solve(normalsat,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.SAT)))
        normalsat = "unsat"
        result, _ = self.normalSolver.solve(normalsat,8)
        self.assertFalse(result.equals(SolverResult(SolverResultType.SAT)))

    def testunsat(self):
        normalunsat = "unsat"
        result, _ = self.normalSolver.solve(normalunsat,8)
        self.assertTrue(result.equals(SolverResultType.UNSAT))
        normalunsat = """
unsat
        """
        result, _ = self.normalSolver.solve(normalunsat,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.UNSAT)))
        normalunsat = """(some text)
unsat
(some text)
        """
        result, _ = self.normalSolver.solve(normalunsat,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.UNSAT)))
        normalunsat = "sat"
        result, _ = self.normalSolver.solve(normalunsat,8)
        self.assertFalse(result.equals(SolverResult(SolverResultType.UNSAT)))

    def testunknown(self):
        normalunknown = "unknown"
        result, _ = self.normalSolver.solve(normalunknown,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.UNSAT)))
        normalunknown = """
unknown
        """
        result, _ = self.normalSolver.solve(normalunknown,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.SAT)))
        normalunknown = """(some text)
unknown
(some text)
        """
        result, _ = self.normalSolver.solve(normalunknown,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.UNKNOWN)))

    def testmultiline(self):
        multiline = """
sat
sat
sat
        """
        result, _ = self.normalSolver.solve(multiline,8)
        oracle = SolverResult()
        oracle.append(SolverResultType.SAT)
        oracle.append(SolverResultType.SAT)
        oracle.append(SolverResultType.SAT)
        self.assertTrue(result.equals(oracle))
        multiline = """
unsat
sat
sat
        """
        result, _ = self.normalSolver.solve(multiline,8)
        oracle = SolverResult()
        oracle.append(SolverResultType.UNSAT)
        oracle.append(SolverResultType.SAT)
        oracle.append(SolverResultType.SAT)
        self.assertTrue(result.equals(oracle))
        multiline = """
unsat
unknown
sat
        """
        result, _ = self.normalSolver.solve(multiline,8)
        oracle = SolverResult()
        oracle.append(SolverResultType.UNSAT)
        oracle.append(SolverResultType.SAT)
        oracle.append(SolverResultType.SAT)
        self.assertTrue(result.equals(oracle))
        multiline = """
unsat
unknown
sat
        """
        result, _ = self.normalSolver.solve(multiline,8)
        oracle = SolverResult()
        oracle.append(SolverResultType.UNSAT)
        oracle.append(SolverResultType.SAT)
        oracle.append(SolverResultType.UNSAT)
        self.assertFalse(result.equals(oracle))

    def testfail(self):
        normalfail = "Couldn't open file:"
        result, _ = self.normalSolver.solve(normalfail,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.FAIL)))

    def testcrash(self):
        empty = ""
        result, _ = self.normalSolver.solve(empty,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.CRASH)))
        random = "dasdsaqhgdbqwuh"
        result, _ = self.normalSolver.solve(random,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.CRASH)))
        segfault = "Segmentation fault"
        result, _ = self.normalSolver.solve(segfault,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.CRASH)))

    def testtimeout(self):
        timeout = "sat"
        result, _ = self.normalSolver.solve(timeout,0)
        self.assertTrue(result.equals(SolverResult(SolverResultType.TIMEOUT)))


    def testignore(self):
        ignore = "Cannot get model"
        result, _ = self.normalSolver.solve(ignore,8)
        self.assertTrue(result.equals(SolverResult(SolverResultType.IGNORED)))

    def testequals(self):
        normalsat = "sat"
        result, _ = self.normalSolver.solve(normalsat,8)
        oracle = SolverResult()
        oracle.append(SolverResultType.UNSAT)
        oracle.append(SolverResultType.SAT)
        oracle.append(SolverResultType.UNSAT)
        self.assertFalse(result.equals(oracle))

        normalsat = """
sat
sat
sat
        """
        result, _ = self.normalSolver.solve(normalsat,8)
        oracle = SolverResult()
        oracle.append(SolverResultType.UNSAT)
        self.assertFalse(result.equals(oracle))

        self.assertFalse(result.equals("sat"))

if __name__ == '__main__':
#     s=SolverTestCase()
#     s.setUp()
#     s.testignore()
    unittest.main()
