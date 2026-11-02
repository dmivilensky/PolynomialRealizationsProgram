"""Focused checks against the polynomial identity and physical models."""

import sys
import unittest
from fractions import Fraction as F
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import predict
import simulate
from common import ADDITIVE, VARIATION, epsilon, fractal_order, prepare, responses, run
from models import CoupledCycles, SpikedRidge


class Tests(unittest.TestCase):
    def test_independent_rational_history(self):
        from rational_reference import run as reference

        for N in (2, 3, 8, 9):
            tape = [F((-1) ** s * (s + 1), 7) for s in range(N)]
            for name in ("flat", "balanced"):
                exact, _ = reference(name, N, F(1, 10), F(2), F(1, 3), tape, F(5), F(2))
                c = prepare(name, N, 0.1, 2.0)
                actual = run(
                    c,
                    np.array([[5.0]]),
                    lambda x, s, tape=tape: (x - 2) / 3 + float(tape[s]),
                )
                self.assertAlmostEqual(actual.item(), float(exact), places=10)

    def test_each_physical_impulse_and_call_count(self):
        for name in dict.fromkeys(ADDITIVE + VARIATION):
            c = prepare(name, 16, 0.1, 2.0)
            p, q, phi = responses(c, [0.3])
            queries = []
            nominal = run(
                c,
                np.array([[5.0]]),
                lambda x, s, queries=queries: queries.append(x.item()) or 0.3 * (x - 2),
            )
            self.assertEqual(len(queries), 16)
            np.testing.assert_allclose(np.array(queries), 2 + 3 * q[:, 0], atol=2e-11)
            self.assertAlmostEqual(nominal.item(), 2 + 3 * p.item(), places=10)
            for j in range(16):
                noisy = run(
                    c,
                    np.array([[5.0]]),
                    lambda x, s, j=j: 0.3 * (x - 2) + (1.0 if s == j else 0.0),
                )
                self.assertAlmostEqual((noisy - nominal).item(), phi[j, 0], places=9)

    def test_exact_terminal_and_published_order(self):
        with self.assertRaises(ValueError):
            fractal_order(12)
        np.testing.assert_array_equal(
            fractal_order(8), np.array([1, 8, 4, 5, 2, 7, 3, 6]) - 1
        )
        for name in ("flat", "balanced", "pref", "lf", "sine"):
            c = prepare(name, 64, 0.01, 1.0)
            for lam in (0.01, 0.37, 1.0):
                result = run(c, np.array([[1.0]]), lambda x, s, lam=lam: lam * x)
                target = epsilon(64, 0.01, 1.0) * np.polynomial.chebyshev.chebval(
                    (1.01 - 2 * lam) / 0.99, [0] * 64 + [1]
                )
                self.assertAlmostEqual(result.item(), target, places=10)

    def test_ridge_data_and_dither_covariance(self):
        p = SpikedRidge(10000, dimension=16)
        A, y, reg = p.design()
        x = np.arange(16) / 16
        for worker in range(p.workers):
            g = (A @ x - y[worker]) @ A / 16 + reg * x
            np.testing.assert_allclose(g, p.apply(x) - p.rhs[worker], atol=2e-14)
        sigma = 0.3 * p.mu
        trials = 12000
        x0 = np.broadcast_to(p.x0, (trials, p.dimension))
        noise = p.quantized_oracle(sigma, 7)(x0, 0) - p.gradient(x0)
        self.assertLess(abs(np.mean(noise**2) * p.dimension / sigma**2 - 1), 0.025)
        self.assertLess(abs(np.mean(noise)), 0.03 * sigma / np.sqrt(p.dimension))

    def test_network_spectrum_projection_and_tangent(self):
        p = CoupledCycles(10000)
        np.testing.assert_allclose(p.apply(p.U.T), p.lam[:, None] * p.U.T, atol=3e-15)
        np.testing.assert_allclose(p.projection(p.U.T), p.U.T, atol=1e-15)
        c = prepare("balanced", 64, p.mu, p.L)
        prediction = predict.variation(c, p)
        initial = np.r_[p.x0, np.zeros(p.dimension)][None, :]
        output = run(c, initial, p.tangent_oracle(prediction["profile"]))[
            0, p.dimension :
        ]
        self.assertLess(abs(np.linalg.norm(output) / prediction["energy"] - 1), 2e-8)

    def test_long_horizon_and_finite_noise(self):
        for kappa in (10000, 40000):
            p = CoupledCycles(kappa)
            c = prepare("balanced", 1024, p.mu, p.L)
            prediction = predict.variation(c, p)
            total, excess, energy = simulate.variation(
                c, p, 0.01 * p.mu, 16, 31, prediction
            )
            self.assertTrue(np.isfinite(total).all() and np.isfinite(excess).all())
            self.assertLess(abs(energy / prediction["energy"] - 1), 1e-4)

    def test_lf_order_invariance_for_commuting_channel(self):
        p = CoupledCycles(100)
        c = prepare("lf", 16, p.mu, p.L)
        reversed_c = {**c, "alpha": c["alpha"][::-1].copy()}
        _, q, phi = responses(c, p.lam)
        _, qr, phir = responses(reversed_c, p.lam)
        np.testing.assert_allclose(q * phi, (qr * phir)[::-1], rtol=2e-9, atol=1e-13)
        rng = np.random.default_rng(4)
        signs = 2 * rng.integers(0, 2, size=16) - 1
        delta = 0.01 * p.mu
        forward = run(
            c,
            p.x0[None, :],
            lambda x, s: p.apply(x) + delta * signs[s] * p.projection(x),
        )
        backward = run(
            reversed_c,
            p.x0[None, :],
            lambda x, s: p.apply(x) + delta * signs[15 - s] * p.projection(x),
        )
        np.testing.assert_allclose(forward, backward, rtol=1e-9, atol=1e-12)


if __name__ == "__main__":
    unittest.main()
