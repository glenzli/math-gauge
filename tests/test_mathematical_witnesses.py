"""Check the explicit finite countermodels, not universal theorem coverage."""

import itertools
import math
import unittest


class FiniteWitnessChecks(unittest.TestCase):
    def check_gauge(self, distances):
        for x, y, z in itertools.product(range(3), repeat=3):
            self.assertEqual(distances[x][x], 0)
            self.assertEqual(distances[x][y], distances[y][x])
            self.assertLessEqual(distances[x][z], distances[x][y] + distances[y][z])
        for x in (0, 1):
            self.assertEqual(distances[x][2], math.inf)

    def test_D002_nonseparating_countermodel(self):
        d = [[0, 0, math.inf], [0, 0, math.inf], [math.inf, math.inf, 0]]
        self.check_gauge(d)
        self.assertEqual(d[0][1], 0)
        self.assertNotEqual(0, 1)

    def test_D003_and_D004_legal_certificates(self):
        d = [[0, 1, math.inf], [1, 0, math.inf], [math.inf, math.inf, 0]]
        self.check_gauge(d)
        f = [0, 0, 2]
        self.assertEqual(f[2], 2)
        self.assertTrue(all(f[x] in (0, 1) for x in (0, 1)))
        for coefficient in (0, 1, 2):
            for x, y in itertools.product((0, 1), repeat=2):
                self.assertLessEqual(d[f[x]][f[y]], coefficient * d[x][y])
        self.assertGreater(d[0][1], 0)
        self.assertLessEqual(d[f[0]][f[1]], d[0][1])
        self.assertFalse(2 <= 1)

    def test_E001_individual_component_classes_do_not_fill_product(self):
        image = {(0, 0), (1, 1)}
        product = set(itertools.product((0, 1), repeat=2))
        self.assertEqual(len(image), 2)
        self.assertEqual(len(product), 4)
        self.assertTrue(image < product)

    def test_E002_cycle_has_no_point_fixed_by_the_map(self):
        f = {0: 1, 1: 0}
        self.assertTrue(all(f[x] != x for x in f))
        self.assertTrue(all(f[f[x]] == x for x in f))


if __name__ == "__main__":
    unittest.main()
