"""Full-C competitors; Python handles parameter validation and oracle binding.

The algorithm controllers, models, history updates and searches execute in C.
The original Python methods remain independent mathematical test references.
"""
from __future__ import annotations

import numpy as np

from xrbench.native.competitor_build import backend_metadata, load_native

_native = load_native()

__all__ = ["solve", "backend_metadata"]


def solve(O, x0, *, native_method, trace=None, **params):
    """Run the chosen published method with unchanged shared oracle accounting."""
    names = {"oaccel", "mslbfgs", "mss", "sr1"}
    if native_method not in names:
        raise ValueError(f"Unknown native competitor {native_method!r}")
    x0 = np.asarray(x0, dtype=float)
    if x0.ndim != 1 or not x0.size:
        raise ValueError("Nonempty one-dimensional point required")
    params = dict(params)
    if native_method == "oaccel":
        if params.pop("nonlinear", "oaccel") != "oaccel":
            raise ValueError("Only O-ACCEL retained")
        precond = params.pop("precond", "B")
        if precond not in {"A", "B"}:
            raise ValueError("Unknown O-ACCEL preconditioner")
        params["precond_A"] = precond == "A"
        if params.get("c2") is None:
            params.pop("c2", None)
    if native_method == "mss":
        init = params.pop("init", "dense")
        if init not in {"dense", "scalar", None}:
            raise ValueError("Unknown MSS initialization")
        params["init_dense"] = init == "dense"
    # Fixed registered choices are checked rather than silently ignored.
    for key, expected in {"mode": "tr", "pd": "pd", "fallback": "sd", "tr_norm": "linf", "gamma": "max"}.items():
        if key in params and params.pop(key) != expected:
            raise ValueError(f"Unsupported native {key}; expected {expected}")
    allowed = {
        "oaccel": {"wmax", "precond_A", "delta", "eps0", "c1", "c2", "maxfev",
                   "stpmin", "stpmax", "xtol"},
        "mslbfgs": {"m", "M", "eps_s", "eps_y", "c1", "c_gold", "exact_last"},
        "mss": {"m", "q", "rank_tol", "r", "init_dense"},
        "sr1": {"m", "q", "rank_tol", "r"},
    }[native_method]
    unknown = set(params) - allowed
    if unknown:
        raise TypeError(f"Unsupported native parameters: {sorted(unknown)}")
    for key in {"m", "M", "q", "wmax", "maxfev"} & params.keys():
        value = params[key]
        if not isinstance(value, (int, np.integer)) or value < 1:
            raise ValueError(f"{key} must be a positive integer")
    if native_method == "mslbfgs":
        if params.get("exact_last", False):
            raise ValueError("The native primary MS-L-BFGS variant uses uniform multisecants")
        for key in ("eps_s", "eps_y"):
            if key in params and not 0 < params[key] < 1:
                raise ValueError(f"{key} must lie in (0,1)")
    return _native.solve(native_method, O, x0, params, trace)
