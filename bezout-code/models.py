"""Two controlled application families with explicit spectra and noise laws."""

import math

import numpy as np


class SpikedRidge:
    """Distributed ridge with one shared factor and weak individual features.

    H=mu I+(1-mu)vv^T, v=1/sqrt(d). Local linear terms differ but
    average to H xstar. This is f_i=||A x-y_i||²/(2d)+reg||x||²/2,
    with A^T A/d=H-reg I (reg=mu/4). Both A and y_i exist explicitly.
    """

    def __init__(self, kappa, dimension=64, workers=4):
        self.mu, self.L, self.dimension, self.workers = (
            1 / kappa,
            1.0,
            dimension,
            workers,
        )
        self.v = np.ones(dimension) / math.sqrt(dimension)
        rng = np.random.default_rng(1701)
        weak = rng.normal(size=dimension)
        weak -= weak.mean()
        weak /= np.linalg.norm(weak)
        self.xstar = math.sqrt(0.9) * weak + math.sqrt(0.1) * self.v
        self.x0 = np.zeros(dimension)
        shifts = rng.normal(size=(workers, dimension))
        shifts -= shifts.mean(axis=0)
        self.rhs = self.apply(self.xstar) + 0.01 * self.mu * shifts
        self.lam = np.array([self.mu, 1.0])
        self.multiplicity = np.array([dimension - 1, 1])
        self.initial_energy = np.array([0.9, 0.1])

    def apply(self, x):
        return self.mu * x + (1 - self.mu) * np.mean(x, axis=-1, keepdims=True)

    def gradient(self, x):
        return self.apply(x - self.xstar)

    def design(self):
        """Explicit least-squares data underlying every worker's quadratic."""
        reg = self.mu / 4
        v = np.outer(self.v, self.v)
        a, b = math.sqrt(self.mu - reg), math.sqrt(1 - reg)
        S = a * np.eye(self.dimension) + (b - a) * v
        inv = np.eye(self.dimension) / a + (1 / b - 1 / a) * v
        return (
            math.sqrt(self.dimension) * S,
            math.sqrt(self.dimension) * self.rhs @ inv,
            reg,
        )

    def nominal(self, p):
        e = self.x0 - self.xstar
        top = np.dot(e, self.v) * self.v
        return self.xstar + p[0] * (e - top) + p[1] * top

    def quantized_oracle(self, sigma, seed):
        rng = np.random.default_rng(seed)
        h = sigma * math.sqrt(12 * self.workers / self.dimension)

        def oracle(x, s):
            hx = self.apply(x)
            answer = np.zeros_like(x)
            for rhs in self.rhs:
                g = hx - rhs
                if sigma:
                    u = rng.uniform(-0.5, 0.5, size=x.shape)
                    g = h * (np.rint(g / h + u) - u)
                answer += g
            return answer / self.workers

        return oracle

    def energy_oracle(self, weights, direction, amplitude):
        return lambda x, s: self.gradient(x) + amplitude * weights[s] * direction


class CoupledCycles:
    """Two cycle networks linked by identical weak inter-layer channels.

    The shared channel changes, not independently sampled unrelated edges:
    H_s=H+delta*xi_s*P, P the projection onto opposite layer readings.
    This commutes with H and preserves the mean. For |delta|<mu all
    inter-layer conductances stay positive. On the active subspace P=I.
    """

    def __init__(self, kappa, width=16):
        self.mu, self.L, self.width = 1 / kappa, 1.0, width
        self.dimension = 2 * width
        self.bridge = 2 / (kappa - 1)
        self.scale = 4 + 2 * self.bridge
        j = np.arange(width)
        vectors = [np.ones(width) / math.sqrt(width)]
        ev = [0.0]
        for k in range(1, width // 2):
            vectors += [
                math.sqrt(2 / width) * np.cos(2 * np.pi * k * j / width),
                math.sqrt(2 / width) * np.sin(2 * np.pi * k * j / width),
            ]
            ev += [2 - 2 * math.cos(2 * np.pi * k / width)] * 2
        vectors.append((-1.0) ** j / math.sqrt(width))
        ev.append(4.0)
        V = np.array(vectors).T
        self.U = np.vstack((V, -V)) / math.sqrt(2)
        self.lam = (np.array(ev) + 2 * self.bridge) / self.scale
        self.lam[0], self.lam[-1] = self.mu, self.L
        rng = np.random.default_rng(2903)
        a = rng.normal(size=width - 2)
        a *= math.sqrt(0.05) / np.linalg.norm(a)
        self.initial = np.r_[math.sqrt(0.475), a, math.sqrt(0.475)]
        self.x0 = self.U @ self.initial
        self.xstar = np.zeros(self.dimension)
        self.endpoint_energy = 0.95

    def apply(self, x):
        left, right = np.split(x, 2, axis=-1)
        bridge = self.bridge * (left - right)
        a = 2 * left - np.roll(left, 1, axis=-1) - np.roll(left, -1, axis=-1) + bridge
        b = (
            2 * right
            - np.roll(right, 1, axis=-1)
            - np.roll(right, -1, axis=-1)
            - bridge
        )
        return np.concatenate((a, b), axis=-1) / self.scale

    def projection(self, x):
        a, b = np.split(x, 2, axis=-1)
        v = (a - b) / 2
        return np.concatenate((v, -v), axis=-1)

    def nominal(self, p):
        return self.U @ (p * self.initial)

    def finite_oracle(self, delta, seed):
        if abs(delta) >= self.mu:
            raise ValueError("Positive channel weights require |delta|<mu.")
        rng = np.random.default_rng(seed)

        def oracle(x, s):
            xi = 2 * rng.integers(0, 2, size=x.shape[:-1] + (1,)) - 1
            return self.apply(x) + delta * xi * self.projection(x)

        return oracle

    def tangent_oracle(self, weights):
        """Differentiate the actual channel oracle; no finite-difference subtraction."""

        def oracle(z, s):
            x, tangent = np.split(z, 2, axis=-1)
            return np.concatenate(
                (self.apply(x), self.apply(tangent) + weights[s] * self.projection(x)),
                axis=-1,
            )

        return oracle
