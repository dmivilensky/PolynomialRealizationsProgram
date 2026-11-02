"""CUTEst adaptor (pycutest 1.8.2; CUTEst 2.7.1 / SIFDecode / MASTSIF from GitHub ralna/*, see env.sh).

    from xrbench.problems.cutest import load_list, make
    for rec in load_list(): P = make(rec['name'], rec['sif'])

Function-only and gradient-only calls use the corresponding native routines.
The shared Oracle owns caching and counts actual computations, including joint calls.
The frozen problem lists retain their selection metadata; stored in the problem-list JSON files.
"""

import json
import os

import numpy as np

from xrbench.paths import ROOT

HERE = os.path.dirname(os.path.abspath(__file__))

ENV_SH = str(ROOT / "env.sh")


def ensure_env():
    """Load missing CUTEst paths and macOS compiler/SDK settings from env.sh."""
    import sys

    keys = ("CUTEST", "SIFDECODE", "MASTSIF", "PYCUTEST_CACHE")
    if sys.platform == "darwin":
        keys += ("CC", "CXX", "SDKROOT", "MACOSX_DEPLOYMENT_TARGET")
    if all(k in os.environ for k in keys):
        return
    # env.sh contains shell defaults and paths relative to its own location.
    # Evaluate it with bash rather than treating shell expressions as literal paths.
    import subprocess

    raw = subprocess.check_output(["bash", "-c", 'source "$1"; env -0', "bash", ENV_SH])
    values = dict(item.split("=", 1) for item in os.fsdecode(raw).split("\0") if "=" in item)
    for key in keys:
        os.environ.setdefault(key, values[key])


def load_list(fn="cutest.json"):
    with open(os.path.join(HERE, fn)) as fh:
        return json.load(fh)["problems"]


def repair_incomplete_cache():
    """Quarantine unfinished builds before a serial prebuild (never while workers run)."""
    import time
    from importlib.machinery import EXTENSION_SUFFIXES
    from pathlib import Path

    ensure_env()
    cache = Path(os.environ["PYCUTEST_CACHE"])
    holder = cache / "pycutest_cache_holder"
    if not holder.is_dir():
        return
    for entry in holder.iterdir():
        if not entry.is_dir() or entry.name == "__pycache__":
            continue
        binary = any(
            p.name.startswith("_pycutestitf") and p.name.endswith(tuple(EXTENSION_SUFFIXES))
            for p in entry.iterdir()
        )
        if (entry / "__init__.py").is_file() and binary:
            continue
        saved = cache / "incomplete_builds"
        saved.mkdir(exist_ok=True)
        destination = saved / f"{entry.name}-{time.time_ns()}"
        entry.rename(destination)
        print(f"Incomplete CUTEst build moved to {destination}; will rebuild", flush=True)


class CutestProblem:
    convex = False  # not certified; the 'quadratic' objective class is recorded in meta
    err_from_f = True
    fstar = None

    def __init__(self, name, sif=None, list_rec=None):
        ensure_env()
        import pycutest

        self.p = pycutest.import_problem(name, sifParams=sif or None, drop_fixed_variables=True)
        self.name = (
            name if not sif else name + "[" + ",".join(f"{k}={v}" for k, v in sif.items()) + "]"
        )
        self.n = int(self.p.n)
        self.x0 = np.array(self.p.x0, dtype=float)
        props = pycutest.problem_properties(name)
        self.meta = dict(
            source="CUTEst",
            sif=sif,
            objective=props.get("objective"),
            degree=props.get("degree"),
            cutest_name=name,
        )
        # These frozen quadratic instances have SPD Hessians, independently checked
        # in diagnostics/2026-10-17-methods/cutest_quadratic_curvature.json.
        certified = {
            "DIXON3DQ": {100, 1000},
            "DQDRTIC": {100, 1000},
            "HILBERTB": {50},
            "TOINTQOR": {50},
            "TRIDIA": {100, 1000},
            "TESTQUAD": {1000},
        }
        self.convex = props.get("objective") == "quadratic" and self.n in certified.get(name, set())
        self.meta["convex_quadratic"] = self.convex
        if list_rec:
            self.meta["t_eval"] = list_rec.get("t_eval")

    def f(self, x):
        return float(self.p.obj(x))

    def grad(self, x):
        return np.asarray(self.p.grad(x), dtype=float).copy()

    def fg(self, x):
        f, g = self.p.obj(x, gradient=True)
        return float(f), np.asarray(g, dtype=float).copy()

    def hvp(self, x, v):
        return np.asarray(self.p.hprod(v, x=x), dtype=float)

    def err_f(self, fx):  # no f*: gradient targets only (kept for the oracle interface)
        return np.inf

    def err(self, x):
        return np.inf


def make(name, sif=None, list_rec=None):
    return CutestProblem(name, sif, list_rec)
