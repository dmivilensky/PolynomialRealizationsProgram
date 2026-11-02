"""C XR/XR-F executor with the same observed-data model and common oracle.

The Python implementation in xr.py is the independent mathematical reference.
This module builds/loads the C extension at import, before campaign timing.
Only oracle calls and optional diagnostics cross the CPython boundary.
"""

from dataclasses import asdict

import numpy as np

from xrbench.methods._xr_model import Parameters
from xrbench.native.build import backend_metadata, load_native

_native = load_native()

__all__ = ["solve", "backend_metadata", "debug_model"]


def solve(
    O,
    x0,
    *,
    values=False,
    m0=10,
    m_max=100,
    q=3,
    inflation=2.0,
    theta=1.0,
    sigma=1e-4,
    epsilon=1e-10,
    eta0=1e-2,
    mu=None,
    L=None,
    window="hermitian",
    probe=True,
    trial="secant",
    split="model",
    floor=False,
    maxbt=80,
    noise_multiplier=100.0,
    rank_multiplier=32.0,
    safeguard=True,
    hook=None,
    trace=None,
    accepted_hook=None,
):
    """Execute the current XR policy in C; ``values=True`` selects XR-F.

    ``accepted_hook(x,f,g,info)`` observes actual accepted advances after the
    iteration marker. Arrays are independent copies. With no hook there is no
    callback or diagnostic copying. Conditional model hooks belong to xr.py's
    independent reference; debug_model exposes the same C model separately.
    Oracle convergence/budget exceptions propagate after native state cleanup.
    """
    if hook is not None:
        raise TypeError(
            "Use the independent xr.py reference for model hooks; native solve supports accepted_hook"
        )
    x0 = np.asarray(x0, dtype=float)
    if x0.ndim != 1:
        raise ValueError("XR requires a one-dimensional initial point")
    params = Parameters(
        m0=m0,
        m_max=m_max,
        q=q,
        inflation=inflation,
        theta=theta,
        sigma=sigma,
        epsilon=epsilon,
        eta0=eta0,
        values=values,
        window=window,
        probe=probe,
        trial=trial,
        split=split,
        floor=floor,
        noise_multiplier=noise_multiplier,
        rank_multiplier=rank_multiplier,
        safeguard=safeguard,
    )
    params.validate(len(x0))
    if not isinstance(maxbt, (int, np.integer)) or maxbt < 1:
        raise ValueError("maxbt must be a positive integer")
    return _native.solve(O, x0, asdict(params), mu, L, maxbt, trace, accepted_hook)


def debug_model(snapshot, params=None):
    """Evaluate a seeded observed-data state for independent model parity tests."""
    params = Parameters() if params is None else params
    if isinstance(params, dict):
        params = Parameters(**params)
    if not isinstance(params, Parameters):
        raise TypeError("Expected XR Parameters or a parameter dictionary")
    params.validate(len(snapshot["x"]))
    return _native.debug_model(snapshot, asdict(params))
