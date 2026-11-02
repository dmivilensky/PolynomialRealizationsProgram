"""Separate function/gradient oracle with a shared four-point value cache.

One unit acquires a point record for f and/or g. The last four EXACT byte keys
cache actual returned values; a complementary f/g request at a cached point
uses the same unit. Revisiting an evicted point costs another unit. Thus n_pts
means point-oracle units, NOT global unique coordinates. Cached values are
copied before returning to solvers. Stateful problems invalidate the cache
on every gradient/HVP, preserving the original sequence of operators.

n_f counts f requests; n_g counts g requests plus HVP equivalents;
n_g_requests excludes HVP. n_f_evals/n_g_evals count calls of
the corresponding problem adapter (adapters may compute f and g together).
Each HVP costs one additional unit and n_hv; Hessian references are reported
separately. Primary costs use actual n_f_evals/n_g_evals, not request counts.
Exact declared threshold hits and bounded display samples are retained.

All methods share identical budgets, scientific time checks (including cache
hits), target definitions and milestones. Converged requires a target at an
actually evaluated point. Native/numerical stops never imply convergence.
"""

import json
import os
import struct
import time
from collections import OrderedDict

import numpy as np

from xrbench.protocol import ORACLE_BUDGET, SCIENTIFIC_SECONDS


class Converged(Exception):
    pass


class Budget(Exception):
    pass


def _finite_json(value):
    if isinstance(value, np.generic):
        value = value.item()
    if isinstance(value, float) and not np.isfinite(value):
        return None
    if isinstance(value, dict):
        return {str(k): _finite_json(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [_finite_json(v) for v in value]
    return value


class Oracle:
    def __init__(
        self,
        prob,
        budget=ORACLE_BUDGET,
        err_tol=None,
        gtol=None,
        max_time=SCIENTIFIC_SECONDS,
        grid=1.12,
        g_levels=None,
        err_levels=None,
        relative_gtol=None,
    ):
        self.p = prob
        self.budget = int(budget)
        self.err_tol = err_tol
        self.gtol = gtol
        self.relative_gtol = relative_gtol
        self.initial_gnorm = None
        self.max_time = max_time
        self.n_f = 0
        self.n_g = 0
        self.n_hv = 0
        self.n_pts = 0
        self.n_it = 0
        self._recent = OrderedDict()  # four actual cached point-oracle records (exact byte keys)
        self._stateful = bool(getattr(prob, "meta", {}).get("stateful"))
        self.n_f_evals = self.n_g_evals = 0
        self.n_fg_evals = 0
        self.f_envelope = []  # every strict best-f improvement, full binary64 precision
        self.hit = None
        self.best_f = np.inf
        self.best_err = np.inf
        self.best_gn = np.inf
        self.hist = []  # (n_pts, n_g, best_f, best_err, best_gn)
        self.trace = []
        self._next_rec = 1.0
        self._grid = grid
        self.t0 = time.perf_counter()
        self._cpu0 = time.process_time()
        self.status = "running"
        self.info = {}
        self._g_levels = sorted([float(v) for v in (g_levels or [])], reverse=True)
        self._e_levels = sorted([float(v) for v in (err_levels or [])], reverse=True)
        self.milestones = {"g": {}, "err": {}}
        self.milestone_values = {"g": {}, "err": {}}
        self._err_ok = getattr(prob, "err_from_f", True) and (
            hasattr(prob, "err") or hasattr(prob, "err_f")
        )
        self._started_wall = time.time()
        self._started_mono = time.monotonic()
        self._progress_path = os.environ.get("XRBENCH_JOB_PROGRESS")
        self._last_progress = -np.inf
        raw = os.environ.get("XRBENCH_F_TRACE_RAW")
        self._raw_trace = open(raw, "wb", buffering=0) if raw else None
        self._checkpoint()

    # ----------------------------------------------------------------- internals
    def _check_time(self):
        self._checkpoint()
        if time.perf_counter() - self.t0 > self.max_time:
            self.status = "time"
            raise Budget("time")

    def _checkpoint(self, force=False):
        """Parent watchdog telemetry; full first-hit data is written separately on every improvement."""
        if not self._progress_path or (not force and time.perf_counter() - self._last_progress < 2):
            return
        self._last_progress = time.perf_counter()
        finite = lambda v: float(v) if np.isfinite(v) else None
        values = dict(
            scientific_started=self._started_wall,
            scientific_started_monotonic=self._started_mono,
            updated=time.time(),
            n_pts=self.n_pts,
            n_f=self.n_f,
            n_g=self.n_g,
            n_hv=self.n_hv,
            n_it=self.n_it,
            best_f=finite(self.best_f),
            best_gn=finite(self.best_gn),
            best_err=finite(self.best_err),
            info=self.info,
            milestones=self.milestones,
            milestone_values=self.milestone_values,
        )
        temporary = self._progress_path + ".tmp"
        with open(temporary, "w") as stream:
            json.dump(_finite_json(values), stream, allow_nan=False)
        os.replace(temporary, self._progress_path)

    def _count_point(self):
        self._check_time()
        self.n_pts += 1
        if self.n_pts > self.budget:
            self.n_pts -= 1
            self.status = "budget"
            raise Budget("evaluations")

    def _point(self, x):
        self._check_time()
        key = np.asarray(x, dtype=float).tobytes()
        if key in self._recent:
            self._recent.move_to_end(key)
            return self._recent[key]
        self._count_point()
        entry = {}
        self._recent[key] = entry
        if len(self._recent) > 4:
            self._recent.popitem(last=False)
        return entry

    def _record(self, force=False):
        if force or self.n_pts >= self._next_rec:
            self.hist.append(
                (
                    self.n_pts,
                    self.n_g,
                    float(self.best_f),
                    float(self.best_err),
                    float(self.best_gn),
                )
            )
            self.trace.append(
                dict(
                    iteration=self.n_it,
                    n_pts=self.n_pts,
                    n_g=self.n_g_evals,
                    n_f=self.n_f_evals,
                    seconds=time.perf_counter() - self.t0,
                    gnorm=float(self.best_gn),
                    error=float(self.best_err),
                    f=float(self.best_f),
                )
            )
            self._next_rec = max(self._next_rec * self._grid, self.n_pts + 1)

    def _milestones(self):
        stamp = None
        for kind, levels, best in (
            ("g", self._g_levels, self.best_gn),
            ("err", self._e_levels, self.best_err),
        ):
            M = self.milestones[kind]
            while levels and best <= levels[0]:
                if stamp is None:
                    stamp = (
                        self.n_pts,
                        self.n_f_evals,
                        self.n_g_evals,
                        self.n_it,
                        time.perf_counter() - self.t0,
                    )
                key = repr(levels.pop(0))  # round-trip threshold; no formatted-key collisions
                M[key] = stamp
                self.milestone_values[kind][key] = float(best)
        if stamp is not None:
            self._checkpoint(force=True)  # preserve exact hits even if the next native call hangs

    def _update(self, x, fx=None, gx=None):
        # A request issued before the deadline may finish after it. Late values
        # must not satisfy targets or improve the competitive f trace.
        self._check_time()
        hit = False
        if fx is not None and np.isfinite(fx):
            if fx < self.best_f:
                self.best_f = fx
                # Only display samples are retained; exact threshold first hits
                # are stored independently in milestones. Never dump all points.
                if len(self.f_envelope) < 128:
                    self.f_envelope.append((self.n_pts, float(fx)))
                if self._raw_trace is not None:
                    self._raw_trace.write(struct.pack("<Qd", self.n_pts, float(fx)))
            if self.err_tol is not None and self._err_ok:
                e = self.p.err_f(fx) if hasattr(self.p, "err_f") else self.p.err(x)
                if e < self.best_err:
                    self.best_err = e
                if e <= self.err_tol:
                    hit = True
        if gx is not None:
            gn = float(np.linalg.norm(gx))
            if self.initial_gnorm is None and np.isfinite(gn):
                self.initial_gnorm = gn
                if self.relative_gtol is not None:
                    self.gtol = self.relative_gtol * max(1.0, gn)
                    self._g_levels = sorted([v * max(1.0, gn) for v in (1e-6, 1e-8)], reverse=True)
            if np.isfinite(gn) and gn < self.best_gn:
                self.best_gn = gn
            if self.gtol is not None and gn <= self.gtol:
                hit = True
            if not getattr(self.p, "err_from_f", True) and hasattr(self.p, "err"):
                e = self.p.err(x)
                if e < self.best_err:
                    self.best_err = e
                if self.err_tol is not None and e <= self.err_tol:
                    hit = True
        if self._g_levels or self._e_levels:
            self._milestones()
        self._record()
        if hit:
            self.status = "converged"
            self.hit = dict(
                n_pts=self.n_pts,
                n_it=self.n_it,
                x=np.asarray(x).tolist(),
                f=float(fx) if fx is not None else None,
                gnorm=float(np.linalg.norm(gx)) if gx is not None else None,
                error=float(e) if self.err_tol is not None and "e" in locals() else None,
            )
            self._record(force=True)
            raise Converged()

    # ----------------------------------------------------------------- public API
    def f(self, x):
        entry = self._point(x)
        self.n_f += 1
        if "f" not in entry:
            self.n_f_evals += 1
            entry["f"] = float(self.p.f(x))
        fx = entry["f"]
        self._update(x, fx=fx)
        return fx

    def g(self, x):
        entry = self._point(x)
        self.n_g += 1
        if "g" not in entry:
            self.n_g_evals += 1
            entry["g"] = np.asarray(self.p.grad(x), dtype=float).copy()
        gx = entry["g"]
        if self._stateful:
            self._recent.clear()  # a gradient changes the problem's state; no stale cache hits
        self._update(x, gx=gx)
        return gx.copy()

    def fg(self, x):
        entry = self._point(x)
        self.n_f += 1
        self.n_g += 1
        if not entry and hasattr(self.p, "fg"):
            fx, gx = self.p.fg(x)
            self.n_fg_evals += 1
            self.n_f_evals += 1
            self.n_g_evals += 1
            entry.update(f=float(fx), g=np.asarray(gx, dtype=float).copy())
        else:
            if "f" not in entry:
                self.n_f_evals += 1
                entry["f"] = float(self.p.f(x))
            if "g" not in entry:
                self.n_g_evals += 1
                entry["g"] = np.asarray(self.p.grad(x), dtype=float).copy()
        fx, gx = entry["f"], entry["g"]
        if self._stateful:
            self._recent.clear()
        self._update(x, fx=fx, gx=gx)
        return fx, gx.copy()

    def hvp(self, x, v):
        """Hessian-vector product (reference methods only); counted as one gradient at a distinct point."""
        self._count_point()
        self.n_g += 1
        self.n_hv += 1
        if self._stateful:
            self._recent.clear()
        value = np.asarray(self.p.hvp(x, v), dtype=float)
        self._check_time()
        return value

    def mark_iter(self):
        self._check_time()
        self.n_it += 1

    def note(self, key, value):
        """Record solver information (stop message, internal counters); never affects the run."""
        self.info[key] = value

    def summary(self):
        self._record(force=True)
        return dict(
            status=self.status,
            n_pts=self.n_pts,
            n_f=self.n_f,
            n_g=self.n_g,
            n_hv=self.n_hv,
            n_it=self.n_it,
            best_f=float(self.best_f),
            best_err=float(self.best_err),
            best_gn=float(self.best_gn),
            time=time.perf_counter() - self.t0,
            hist=self.hist,
            cpu_time=time.process_time() - self._cpu0,
            milestone_values=self.milestone_values,
            milestones=self.milestones,
            info=self.info,
            f_envelope=self.f_envelope,
            hit=self.hit,
            n_f_evals=self.n_f_evals,
            n_g_evals=self.n_g_evals,
            n_fg_evals=self.n_fg_evals,
            initial_gnorm=self.initial_gnorm,
            target_gnorm=self.gtol,
            trace=self.trace,
            n_g_requests=self.n_g - self.n_hv,
            cost_protocol="separate-f-g-cache4-v3",
        )


def run_method(solve, prob, x0, params=None, **oracle_kw):
    """Run solve(oracle, x0, **params) until Converged / Budget / natural termination."""
    O = Oracle(prob, **oracle_kw)
    try:
        solve(O, np.array(x0, dtype=float), **(params or {}))
        O.status = "method_stop"
        O.info.setdefault("stop", O.info.get("message", "solver_returned"))
    except Converged:
        O.status = "converged"
    except Budget:
        pass
    except Exception as ex:  # a method failure is a result, not a crash of the benchmark
        O.status = "error:" + type(ex).__name__ + ":" + str(ex)[:120]
    return O.summary()
