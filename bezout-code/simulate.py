"""Monte Carlo trajectories and deterministic gain measurements."""

import numpy as np
from common import run


def additive(c, problem, sigma, trials, seed, pred):
    x0 = np.broadcast_to(problem.x0, (trials, problem.dimension))
    out = run(c, x0, problem.quantized_oracle(sigma, seed))
    errors = np.sum((out - problem.xstar) ** 2, axis=1)
    excess = np.sum((out - pred["nominal"]) ** 2, axis=1)
    # Actual worst-case temporal-energy perturbation, in the maximizing mode.
    oracle = problem.energy_oracle(pred["profile"], pred["direction"], problem.mu)
    endpoint = run(c, problem.xstar[None, :], oracle)[0]
    gain = np.linalg.norm(endpoint - problem.xstar) / problem.mu
    return errors, excess, float(gain)


def variation(c, problem, delta, trials, seed, pred):
    initial = np.r_[problem.x0, np.zeros(problem.dimension)][None, :]
    tangent = run(c, initial, problem.tangent_oracle(pred["profile"]))[
        0, problem.dimension :
    ]
    measured_energy = float(np.linalg.norm(tangent))
    x0 = np.broadcast_to(problem.x0, (trials, problem.dimension))
    out = run(c, x0, problem.finite_oracle(delta, seed))
    excess = np.sum((out - pred["nominal"]) ** 2, axis=1)
    total = np.sum(out * out, axis=1)
    # Check roundoff against the perturbation signal actually being measured.
    nominal = run(c, problem.x0[None, :], lambda x, s: problem.apply(x))[0]
    defect = np.linalg.norm(nominal - pred["nominal"])
    if defect > 0.02 * delta * np.sqrt(pred["gamma"]):
        raise ArithmeticError(
            f"{c['method']}, N={c['N']}: roundoff obscures the selected noise scale."
        )
    return total, excess, measured_energy
