"""Exact odd-horizon checks on signed, parity-mixing polynomial bases."""

import random
import sys
import unittest
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from rational_reference import add, expand, multiply, scale, value

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import epsilon, prepare, responses, run


def chebyshev(N):
    polynomials = [[F(1)], [F(0), F(1)]]
    for _ in range(2, N + 1):
        polynomials.append(
            add(
                scale(multiply([F(0), F(1)], polynomials[-1]), F(2)),
                scale(polynomials[-2], F(-1)),
            )
        )
    return polynomials


def factors(terminal, basis):
    """Expand the divided difference directly, in the supplied graded basis."""
    N = len(basis)
    response = [[F(0)] * (N - s) for s in range(N)]
    for a in range(N):
        coefficients = expand([terminal[a + b + 1] / 2 for b in range(N - a)], basis)
        for s in range(N - a):
            response[s][a] = coefficients[s]
    return response


def corner_energies(response, basis):
    diagonal, cross, symmetric = F(0), F(0), F(0)
    for f, q in zip(response, basis):
        fp, fm, qp, qm = (
            value(f, F(1)),
            value(f, F(-1)),
            value(q, F(1)),
            value(q, F(-1)),
        )
        diagonal += (fp * qp) ** 2 + (fm * qm) ** 2
        cross += (fp * qm) ** 2 + (fm * qp) ** 2
        symmetric += (fp * qm + fm * qp) ** 2
    return F(3, 8) * diagonal + cross / 8, F(3, 8) * diagonal + symmetric / 16


class OddOptimumTests(unittest.TestCase):
    def test_physical_odd_tangent_reaches_sharp_gain(self):
        mu, L = 1e-4, 1.0
        for N in (3, 9, 65, 255, 1023):
            method = prepare("balanced", N, mu, L)
            _, query, response = responses(method, [mu])
            profile = (query * response)[:, 0]
            gain = np.linalg.norm(profile)
            target = (
                2
                * epsilon(N, mu, L)
                * N**1.5
                / (L - mu)
                * np.sqrt(1 + (N - 1) / ((N + 1) * N**2))
            )
            self.assertAlmostEqual(gain / target, 1.0, places=10)
            profile /= gain

            def tangent_oracle(x, s, profile=profile):
                return np.array([mu * x[0], mu * x[1] + profile[s] * x[0]])

            derivative = run(method, np.array([1.0, 0.0]), tangent_oracle)[1]
            self.assertLess(abs(derivative / target - 1), 2e-6)

    def test_signed_parity_mixing_factorizations(self):
        rng = random.Random(190321)
        for N in (3, 5, 7, 9):
            T = chebyshev(N)
            lower = F(N**3, 4) * (1 + F(N - 1, (N + 1) * N**2))
            for _ in range(12):
                basis = []
                for s in range(N):
                    q = T[s][:]
                    for j in range(s):
                        q = add(q, scale(T[j], F(rng.randint(-5, 5), 7)))
                    basis.append(q)
                response = factors(T[N], basis)
                for x, y in ((F(1), F(-1)), (F(2, 3), F(-3, 4)), (F(-1), F(-1))):
                    expected = (
                        (value(T[N], x) - value(T[N], y)) / (2 * (x - y))
                        if x != y
                        else F(N**2, 2)
                    )
                    actual = sum(
                        value(f, x) * value(q, y) for f, q in zip(response, basis)
                    )
                    self.assertEqual(actual, expected)
                original, symmetric = corner_energies(response, basis)
                self.assertGreaterEqual(original, symmetric)
                self.assertGreaterEqual(symmetric, lower)

    def test_balanced_attains_both_four_corner_bounds(self):
        for N in (3, 5, 7, 9, 11):
            T = chebyshev(N)
            basis = T[:2]
            for s in range(2, N):
                omega = (
                    F((N + 1) * (N + 1 - s), N**2 + 1)
                    if s % 2 == 0
                    else F(N + 2 - s, N + 1)
                )
                basis.append(
                    add(basis[s - 2], scale(add(T[s], scale(T[s - 2], F(-1))), omega))
                )
            response = factors(T[N], basis)
            target = F(N**3, 4) * (1 + F(N - 1, (N + 1) * N**2))
            self.assertEqual(corner_energies(response, basis), (target, target))
            for x in (F(-1), F(1)):
                for y in (F(-1), F(1)):
                    self.assertEqual(
                        sum(
                            (value(f, x) * value(q, y)) ** 2
                            for f, q in zip(response, basis)
                        ),
                        target,
                    )
            for s, (f, q) in enumerate(zip(response, basis)):
                mass = F(N**2 + 1, 2 * (N + 1)) if s % 2 == 0 else F(N + 1, 2)
                self.assertEqual(value(f, F(1)) * value(q, F(1)), mass)


if __name__ == "__main__":
    unittest.main()
