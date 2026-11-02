"""Shared observed-data model with practical or diagnostic curvature policies.

All matrices use pair-norm coordinates. Congruences and a QR basis implement
exactly the displayed formulas without squaring the condition number of S.
The secant policy uses only the newest positive observed Rayleigh quotient.
The midpoint diagnostic additionally implements the printed Ritz/Schur rule.
The only rank tolerance is an explicit floating-point independence decision;
there is no ridge, eigenvalue floor, pseudoinverse or changed secant equation.
"""

import math
from dataclasses import dataclass, field
from functools import lru_cache

import numpy as np
from scipy.linalg import (
    cho_factor,
    cho_solve,
    eigvalsh,
    norm,
    qr,
    qr_delete,
    qr_insert,
    solve_triangular,
)
from scipy.linalg.lapack import get_lapack_funcs, zpotrf

from xrbench.methods._gram import WindowGram


@dataclass(frozen=True)
class Parameters:
    m0: int = 10
    m_max: int = 100
    q: int = 3
    inflation: float = 2.0
    theta: float = 1.0
    sigma: float = 1e-4
    epsilon: float = 1e-10
    eta0: float = 1e-2
    values: bool = False
    window: str = "hermitian"
    probe: bool = True
    trial: str = "secant"
    split: str = "model"
    floor: bool = False
    noise_multiplier: float = 100.0
    rank_multiplier: float = 32.0
    safeguard: bool = True

    def validate(self, dimension):
        if dimension < 1 or not 1 <= self.m0 <= self.m_max:
            raise ValueError("require 1 <= m0 <= m_max and a nonempty problem")
        if self.q < 1 or int(self.q) != self.q or self.inflation <= 1 or self.theta <= 0:
            raise ValueError("invalid memory, inflation or window threshold")
        if not 0 < self.sigma < 0.5 or not 0 < self.epsilon < 1:
            raise ValueError("invalid Armijo or safeguard margin")
        if not 0 < self.eta0 < 1 - 2 * self.sigma:
            raise ValueError("invalid adequacy margin")
        if self.window not in {"hermitian", "positive"}:
            raise ValueError("window must be hermitian or positive")
        if self.trial not in {"secant", "midpoint", "lagged"} or self.split not in {
            "model",
            "euclidean",
        }:
            raise ValueError("invalid trial or value split ablation")
        if self.noise_multiplier < 0 or self.rank_multiplier <= 0:
            raise ValueError("invalid floating-point tolerances")


@lru_cache(maxsize=128)
def _strict_lower_indices(size):
    return np.tril_indices(size, -1)


def latest(C):
    """T_ij = s_min(i,j)^T y_max(i,j), in chronological order."""
    result = C.copy()
    i, j = _strict_lower_indices(len(C))
    result[i, j] = C[j, i]
    # Match the original addition of discarded-triangle zeros, including
    # the sign of an exactly zero pairing; no numerical formula changes.
    result += 0
    return result


def trapezoid_defect(fa, ft, ga, gt, step, noise_multiplier=100.0):
    """Compensated endpoint defect, with the manuscript's machine-noise gate."""
    left, right = float(ga @ step), float(gt @ step)
    if not all(math.isfinite(v) for v in (fa, ft, left, right)):
        return math.nan
    scale = max(abs(fa), abs(ft), abs(left), abs(right))
    if scale == 0:
        return 0.0
    try:
        delta = math.fsum((ft, -fa, -0.5 * left, -0.5 * right))
    except OverflowError:
        delta = scale * math.fsum(
            (ft / scale, -fa / scale, -0.5 * left / scale, -0.5 * right / scale)
        )
    noise = (
        noise_multiplier
        * np.finfo(float).eps
        * scale
        * (abs(fa / scale) + abs(ft / scale) + abs(left / scale) + abs(right / scale))
    )
    return 0.0 if abs(delta) <= noise else delta


@dataclass(eq=False)
class Pair:
    """Actual observation with scalar covectors transported to the current anchor.

    ``pairing`` and ``delta`` are phi/||s||^2 and defect/||s||^2;
    ``euclidean`` is s^T(x-a)/||s||^2. These cached coordinates avoid repeated
    subtraction of nearly equal points. The actual step/image remain immutable.
    """

    step: np.ndarray
    image: np.ndarray
    scale: float
    s: np.ndarray
    y: np.ndarray
    delta: float
    pairing: float = 0.0
    euclidean: float = 0.0

    @classmethod
    def observe(cls, step, image, delta=0.0):
        scale = float(norm(step, check_finite=False))
        if not scale > 0 or not math.isfinite(scale):
            return None
        s, y = np.asarray(step, float) / scale, np.asarray(image, float) / scale
        if not np.all(np.isfinite(y)) or not float(s @ y) > 0:
            return None
        return cls(step.copy(), image.copy(), scale, s, y, float(delta / scale / scale))

    def transport(self, displacement):
        coordinate = displacement / self.scale
        self.pairing += float(self.y @ coordinate)
        self.euclidean += float(self.s @ coordinate)


class WindowAlgebra:
    """Maintain chronological Gram overlaps and the newest-first QR basis.

    Appending one observation and deleting oldest columns use QR updates.
    A fresh QR is used if an insertion is numerically dependent, and after
    50 updates to prevent accumulated loss of orthogonality. No oracle calls.
    """

    def __init__(self):
        self.pairs = []
        self.Q = self.R = None
        self.updates = 0
        self.gram = WindowGram()

    def basis(self, pairs, S):
        if not self.pairs or self.updates >= 50:
            self.updates = 0
            return qr(S[:, ::-1], mode="economic", check_finite=False)
        old = {id(pair): i for i, pair in enumerate(self.pairs)}
        start = old.get(id(pairs[0]))
        shared = 0 if start is None else min(len(self.pairs) - start, len(pairs))
        if start is None or any(pairs[i] is not self.pairs[start + i] for i in range(shared)):
            self.updates = 0
            return qr(S[:, ::-1], mode="economic", check_finite=False)
        Q, R = self.Q, self.R
        try:
            if len(self.pairs) > shared:
                Q, R = qr_delete(
                    Q, R, shared, p=len(self.pairs) - shared, which="col", check_finite=False
                )
            for pair in pairs[shared:]:
                Q, R = qr_insert(Q, R, pair.s, 0, which="col", check_finite=False)
            self.updates += 1
            return Q, R
        except np.linalg.LinAlgError:
            self.updates = 0
            return qr(S[:, ::-1], mode="economic", check_finite=False)

    def remember(self, pairs, Q, R):
        self.pairs, self.Q, self.R = list(pairs), Q, R


@dataclass
class State:
    x: np.ndarray
    f: float
    g: np.ndarray
    capacity: int
    tau0: float
    c1: float
    c2: float
    pairs: list = field(default_factory=list)
    clean: int = 0
    bounds: tuple | None = None
    secant_curvature: float | None = None
    lagged: float | None = None
    iteration: int = 0
    counters: dict = field(
        default_factory=lambda: dict(
            nrej=0,
            nbt=0,
            nprobe=0,
            nskip=0,
            nsafe=0,
            nrank_deleted=0,
            nwindow_deleted=0,
            nF_applied=0,
            nF_fallback=0,
            nF_omitted=0,
            ninterval_empty=0,
            nnumerical=0,
        )
    )
    window_sum: int = 0
    model_calls: int = 0
    max_window: int = 0
    memory_changes: int = 0
    maximum_capacity: int = 0
    algebra: WindowAlgebra = field(default_factory=WindowAlgebra)


def _positive(H):
    try:
        cho_factor(H, lower=True, check_finite=False)
        return True
    except np.linalg.LinAlgError:
        return False


def unrefuted_suffix(C, theta=1.0, window="hermitian"):
    """Reverse Cholesky: number of oldest pairs excluded by the window test.

    The caller retains the newest positive-curvature pair. Diagonal congruence
    makes the certificate invariant under pair scaling, including signed scales.
    """
    p = len(C)
    if p == 0:
        return 0
    diagonal = np.sqrt(np.abs(np.diag(C)))
    if np.any(diagonal == 0) or not np.all(np.isfinite(C)):
        return p
    N = C / diagonal[:, None] / diagonal[None, :]
    H = latest(N).astype(complex)
    if window == "hermitian":
        H += (1j / theta) * (N - N.T)
    _, info = zpotrf(np.array(H[::-1, ::-1], order="F"), lower=True, clean=False, overwrite_a=True)
    return 0 if info == 0 else p - info + 1


def value_model(pairs, C, params, *, base=None):
    """Literal storedValueTerm: omit an oversized term, never clip it."""
    terms = np.zeros(len(pairs))
    omitted = 0
    for i, pair in enumerate(pairs):
        ci = C[i, i]
        split = (pair.pairing / ci if params.split == "model" else pair.euclidean) - 0.5
        term = 12.0 * split * pair.delta
        if not math.isfinite(term) or abs(term) > ci / 2:
            omitted += int(term != 0)
        else:
            terms[i] = term
    return (latest(C) if base is None else base) - np.diag(terms), terms, omitted


def update_capacity(params, dimension, capacity, clean, first_pairs, first_deleted, evaluations):
    """Exact AlgorithmState.updateCapacity, including integer floor-halving."""
    if first_deleted >= max(1, (first_pairs + 1) // 2):
        return max(min(params.m0, dimension), capacity // 2), 0
    clean = (
        clean + 1
        if evaluations == 1 and first_deleted == 0 and first_pairs == min(capacity, dimension)
        else 0
    )
    if clean == params.q:
        return min(capacity + min(params.m0, dimension), params.m_max, dimension), 0
    return capacity, clean


@dataclass
class ModelResult:
    u: np.ndarray
    first_pairs: int
    deleted: int
    virtual_x: np.ndarray
    virtual_g: np.ndarray
    direction: np.ndarray
    rho: float | None
    safeguarded: bool = False


def fallback_curvature(state, params):
    """Use running spectral bounds only for the explicit midpoint diagnostic."""
    if params.trial == "midpoint" and state.bounds is not None:
        return state.bounds[0] / 2 + state.bounds[1] / 2
    return state.secant_curvature if state.secant_curvature is not None else 1 / state.tau0


def _symmetric_solve(A, b, positive=False):
    """Equilibrated solution of the unchanged system; no regularization."""
    scales = np.sqrt(np.abs(np.diag(A)))
    if np.any(scales == 0):
        scales = np.where(scales > 0, scales, 1.0)
    B = A / scales[:, None] / scales[None, :]
    rhs = b / scales
    if positive:
        answer = cho_solve(
            cho_factor(B[::-1, ::-1], lower=True, check_finite=False), rhs[::-1], check_finite=False
        )[::-1]
    else:
        answer = np.linalg.solve(B, rhs)
    return answer / scales


def _orthogonal_model(T, R):
    """R^-T T R^-1, with R from the newest-first QR basis."""
    left = solve_triangular(R.T, T[::-1, ::-1], lower=True, check_finite=False)
    transformed = solve_triangular(R.T, left.T, lower=True, check_finite=False).T
    return (transformed + transformed.T) / 2


def consistency_interval(Tq, Q, d, bounds):
    """Literal shifted-Schur endpoints, in a numerically stable orthonormal basis."""
    lower, upper = bounds
    unit = d / norm(d, check_finite=False)
    b = Q.T @ unit
    low = lower + lower * lower * float(
        b @ _symmetric_solve(Tq - lower * np.eye(len(Tq)), b, positive=True)
    )
    high = upper - upper * upper * float(
        b @ _symmetric_solve(upper * np.eye(len(Tq)) - Tq, b, positive=True)
    )
    return low, high


def model_step(state, params, hook=None):
    """The concrete ModelStep; mutates only retained pairs, bounds and diagnostics."""
    n = len(state.x)
    if state.pairs:
        # Positive observations are immutable. Read the newest one before
        # any suffix selection, and retain this fresh scale if the window
        # later becomes empty. There is no historical maximum in this path.
        fresh = float(state.pairs[-1].s @ state.pairs[-1].y)
        if fresh > 0 and math.isfinite(fresh):
            state.secant_curvature = fresh
    state.pairs = state.pairs[-min(state.capacity, n) :]
    if state.pairs:
        S = np.asarray([pair.s for pair in state.pairs]).T.copy(order="C")
        Q, R = state.algebra.basis(state.pairs, S)
        diagonal = np.abs(np.diag(R))
        threshold = params.rank_multiplier * np.finfo(float).eps * max(S.shape)
        bad = np.flatnonzero(diagonal <= threshold)
        retained = int(bad[0]) if len(bad) else len(state.pairs)
        # The projected metric contains R^-T T R^-1. Requiring a resolvable
        # squared condition number avoids amplifying endpoint roundoff into a
        # fictitious negative Ritz value. This is numerical rank cleanup, not
        # regularization of the secant equation. Check newest-first prefixes,
        # so exactly a chronological suffix survives.
        trcon = get_lapack_funcs("trcon", (R,))
        resolution = params.rank_multiplier * np.sqrt(np.finfo(float).eps)
        while retained:
            reciprocal, info = trcon(R[:retained, :retained], norm="1", uplo="U", diag="N")
            if info == 0 and reciprocal > resolution:
                break
            retained -= 1
        rank_deleted = len(state.pairs) - retained
        if rank_deleted:
            state.counters["nrank_deleted"] += rank_deleted
            state.pairs = state.pairs[rank_deleted:]
            S = S[:, rank_deleted:]
            Q, R = Q[:, :retained], R[:retained, :retained]
    p_mem = len(state.pairs)
    deleted = 0
    rho = None
    virtual_x, virtual_g = state.x.copy(), state.g.copy()
    direction = -state.g.copy()
    if p_mem:
        Y = np.asarray([pair.y for pair in state.pairs]).T.copy(order="C")
        C = state.algebra.gram.get(
            [pair.s for pair in state.pairs], [pair.y for pair in state.pairs], Sm=S, Ym=Y
        )
        deleted = min(unrefuted_suffix(C, params.theta, params.window), p_mem - 1)
        if deleted:
            state.pairs = state.pairs[deleted:]
            S, Y, C = S[:, deleted:], Y[:, deleted:], C[deleted:, deleted:]
            p = len(state.pairs)
            Q, R = Q[:, :p], R[:p, :p]
            state.counters["nwindow_deleted"] += deleted
        state.algebra.remember(state.pairs, Q, R)
        T = latest(C)
        selected = T
        if params.values:
            corrected, terms, omitted = value_model(state.pairs, C, params, base=T)
            state.counters["nF_omitted"] += omitted
            if np.any(terms):
                diagonal = np.sqrt(np.diag(C))
                H = corrected / diagonal[:, None] / diagonal[None, :]
                H = H.astype(complex) + (1j / params.theta) * (
                    (C - C.T) / diagonal[:, None] / diagonal[None, :]
                )
                if _positive(H):
                    selected = corrected
                    state.counters["nF_applied"] += 1
                else:
                    state.counters["nF_fallback"] += 1
        coefficients = -_symmetric_solve(selected, S.T @ state.g, positive=True)
        correction = S @ coefficients
        virtual_x = state.x + correction
        virtual_g = state.g + Y @ coefficients
        if params.trial == "midpoint":
            Tq = _orthogonal_model(T, R)
            extremes = eigvalsh(Tq, check_finite=False, subset_by_index=[0, len(Tq) - 1])
            if not extremes[0] > 0 or not np.all(np.isfinite(extremes)):
                raise np.linalg.LinAlgError(
                    "nonpositive computed Ritz value after rank/window tests"
                )
            lo, hi = float(extremes[0] / params.inflation), float(extremes[-1] * params.inflation)
            state.bounds = (
                (lo, hi)
                if state.bounds is None
                else (min(state.bounds[0], lo), max(state.bounds[1], hi))
            )
        direction = np.zeros(n)
        if len(state.pairs) < n:
            try:
                beta = _symmetric_solve(C.T, Y.T @ virtual_g)
                direction = -virtual_g + S @ beta
            except np.linalg.LinAlgError:
                direction = -virtual_g
            dnorm = float(norm(direction, check_finite=False))
            if dnorm > 0:
                if params.trial == "midpoint":
                    low, high = consistency_interval(Tq, Q, direction, state.bounds)
                    rho = low / 2 + high / 2
                    if low > high:
                        state.counters["ninterval_empty"] += 1
                        rho = float(np.clip(rho, *state.bounds))
                    if params.floor and high > 0:
                        c_armijo = 2 * (1 - params.sigma) - params.eta0
                        rho = min(max(rho, high / c_armijo), high)
                else:
                    rho = fallback_curvature(state, params)
                    if params.trial == "lagged" and state.lagged is not None:
                        rho = state.lagged
                        active = np.diag(C)
                        rho = float(np.clip(rho, np.min(active), np.max(active)))
                if not math.isfinite(rho) or not rho > 0:
                    raise np.linalg.LinAlgError("nonpositive computed trial curvature")
                unit = direction / dnorm
                u = correction - (float(state.g @ unit) / rho) * unit
            else:
                u = correction
        else:
            u = correction
    else:
        state.algebra.remember([], None, None)
        rho = fallback_curvature(state, params)
        u = -state.g / rho
    state.window_sum += len(state.pairs)
    state.model_calls += 1
    state.max_window = max(state.max_window, len(state.pairs))
    if hook is not None:
        hook(virtual_x, virtual_g, len(state.pairs))
    safeguarded = False
    if params.safeguard:
        gnorm = float(norm(state.g, check_finite=False))
        unorm = float(norm(u, check_finite=False))
        if (
            not np.all(np.isfinite(u))
            or float(state.g @ u) > -state.c1 * gnorm**2
            or unorm > state.c2 * gnorm
        ):
            fallback = fallback_curvature(state, params)
            fallback = float(np.clip(fallback, 1 / state.c2, 1 / state.c1))
            u = -state.g / fallback
            state.counters["nsafe"] += 1
            safeguarded = True
    return ModelResult(u, p_mem, deleted, virtual_x, virtual_g, direction, rho, safeguarded)
