"""Finite bias and noise predictions for the two experimental models."""

import numpy as np
from common import responses


def additive(c, problem, sigma):
    p, _, phi = responses(c, problem.lam)
    variance = np.sum(phi * phi, axis=0)
    bias = float(np.dot(problem.initial_energy, p * p))
    noise = float(
        sigma * sigma / problem.dimension * np.dot(problem.multiplicity, variance)
    )
    at = int(np.argmax(variance))
    profile = phi[:, at] / np.sqrt(variance[at])
    direction = (
        problem.v
        if at
        else (problem.xstar - np.dot(problem.xstar, problem.v) * problem.v)
        / np.sqrt(0.9)
    )
    return {
        "mse": bias + noise,
        "bias": bias,
        "noise": noise,
        "energy": float(np.sqrt(variance[at])),
        "profile": profile,
        "direction": direction,
        "nominal": problem.nominal(p),
    }


def variation(c, problem):
    p, query, response = responses(c, problem.lam)
    transfer = (
        query * response * problem.initial[None, :]
    )  # time × active spectral mode
    _, singular_values, directions = np.linalg.svd(transfer.T, full_matrices=False)
    return {
        "energy": float(singular_values[0]),
        "gamma": float(np.sum(transfer * transfer)),
        "profile": directions[0],
        "nominal": problem.nominal(p),
    }


def serializable(record):
    """Keep scalar predictions in JSON; temporal profiles are reconstructed when needed."""
    return {key: float(value) for key, value in record.items() if np.isscalar(value)}
