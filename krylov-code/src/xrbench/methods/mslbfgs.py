"""Multi-secant limited-memory BFGS with polar kernels and symmetric damping.

[G26] F. V. Gubarev, A Multi-Secant Limited-Memory BFGS Method, Optimization
Online, 7 March 2026 (preprint; no journal DOI assigned),
https://optimization-online.org/2026/03/a-multi-secant-limited-memory-bfgs-method/,
https://optimization-online.org/wp-content/uploads/2026/03/ms-lbfgs.pdf.
Primary preset is the uniform variant L=M=8, eps_s=1e-2, eps_y=1e-3 (Section 5).

Equations (9)--(10): polar-kernel block BFGS updates. Equations (18)--(21):
adaptive window and symmetric damping. Equation (44): compact inverse model;
Section 4.4: scalar initialization. The source's Armijo/unit-step and initial
Goldstein search are retained. Function values are requested during Armijo;
gradients only at accepted points. The shared oracle sets stopping/budgets.

Explicit choices where the paper leaves implementation details open:
* Armijo c1=1e-4, quadratic contraction guarded to [.1,.5], max 100 trials;
  Goldstein c=.25, initial 1/||g||, expansion [2,10], bracket bisection.
* Failed searches reset once to Goldstein steepest descent, then terminate.
* Keep the newest L pairs and the longest suffix of imposed block updates
  fully contained in them (memory cut at a block boundary, Figure 1).
* Damping solves the defining constraints (20)--(21) directly on [0,.5]^2
  via quadratic roots along rays and angular minimization, rather than the
  activity-pattern Newton solver sketched in Section 5. Degenerate pairs skip.
* Polar factors use SVD; compact positive factors use QR and triangular solves,
  avoiding a squared-condition Gram matrix. No ridge or curvature clipping.
* Kernel factorization failure retries smaller windows through (18)--(19),
  then the single-pair damping rule. An undefined compact factor terminates
  as numerical failure, without silently changing the Hessian approximation.

The exact-newest reference option uses (14)--(16) and the upper bound (22).
Independent dense block recursions, inverse consistency, kernel factorizations,
window tests and damping feasibility/minimality are tested in test_mslbfgs.py.
No complete Python solver in this module is claimed formally verified.
"""

import numpy as np

EPS_S = 1e-2  # [G26] Sec. 5 default
EPS_Y = 1e-3  # [G26] Sec. 5 default


# ------------------------------------------------------------------------------------------ kernels
def reversed_cholesky(K):
    """K = r r^T with r UPPER triangular ([G26] eq. (42), "reversed Cholesky")."""
    Lc = np.linalg.cholesky(K[::-1, ::-1])  # J K J = Lc Lc^T, J = exchange matrix
    return Lc[::-1, ::-1]  # r = J Lc J is upper triangular, r r^T = K


def _triu_solve(r, B):
    """r^{-1} B for the small upper-triangular r (numpy LAPACK gesv; scipy's solve_triangular is
    anomalously slow for tiny matrices in this environment)."""
    return np.linalg.solve(r, B)


def _inv_from_rchol(K):
    """K^{-1} = r^{-T} r^{-1} with the reversed Cholesky factor (compact form (44): R^{-T} R^{-1})."""
    r = reversed_cholesky(K)
    ri = _triu_solve(r, np.eye(K.shape[0]))
    return ri.T @ ri, r


def polar_kernels(O):
    """K_R = (O O^T)^{1/2}, K_L = (O^T O)^{1/2} ([G26] Sec. 2.1) from the SVD O = U diag(sig) V^T."""
    U, sig, Vt = np.linalg.svd(O)
    KR = (U * sig) @ U.T
    KL = (Vt.T * sig) @ Vt
    return KR, KL, sig, U, Vt


def _polar_right_factor(sig, U):
    """K_R = r r^T via QR of the SVD square root, without forming a Gram."""
    root = np.sqrt(sig)[:, None] * U.T
    R = np.linalg.qr(root[:, ::-1], mode="reduced")[1]
    signs = np.where(np.diag(R) < 0, -1.0, 1.0)
    R = signs[:, None] * R
    return R.T[::-1, ::-1]


def _kernels(O, exact_last, return_root=False):
    """Polar kernels (9)/(14)/(16), retaining positive square-root factors.

    Optional root satisfies Ninv = root.T @ root. No Cholesky of a formed
    inverse Gram is needed when rebuilding the compact approximation.
    """
    U, sig, Vt = np.linalg.svd(O)
    if not (np.all(np.isfinite(sig)) and sig[-1] > 0):
        raise np.linalg.LinAlgError("singular polar kernel")
    rR = _polar_right_factor(sig, U)
    root = _triu_solve(rR, np.eye(len(O)))
    if exact_last:
        mm = len(O) - 1
        Omm = O[mm, mm]
        if not Omm > 0:
            raise np.linalg.LinAlgError("O_mm <= 0 in exact-secant kernel")
        pi = np.eye(len(O))
        pi[:, mm] -= O[:, mm] / Omm
        e = np.eye(len(O))[mm]
        root = np.vstack([root @ pi, e[None, :] / np.sqrt(Omm)])  # literal (14)
        ot = O[mm, :]
        pit = np.eye(len(O))
        pit[mm, :] -= ot / Omm
        left = np.vstack(
            [(np.sqrt(sig)[:, None] * Vt) @ pit, ot[None, :] / np.sqrt(Omm)]
        )  # factor of (16)
        R = np.linalg.qr(left, mode="reduced")[1]
        Ri = np.linalg.solve(R, np.eye(len(O)))
        C = Ri @ Ri.T
    else:
        C = (Vt.T / sig) @ Vt
    Ninv = root.T @ root
    answer = (Ninv, C, rR)
    return answer + (root,) if return_root else answer


def _gamma_star(O, Ym, rR=None):
    """gamma* = ||r_m^{-1} O_m||_F^2 / ||Y_m||_F^2  ([G26] Sec. 4.4)."""
    if rR is None:
        KR = polar_kernels(O)[0]
        rR = reversed_cholesky(0.5 * (KR + KR.T))
    Z = _triu_solve(rR, O)
    return float(np.sum(Z * Z) / np.sum(Ym * Ym))


# ------------------------------------------------------------------- dense reference updates (tests)
def ms_bfgs_update_H(H, S, Y, exact_last=False):
    """Dense MS-BFGS inverse update: eq. (9) (uniform) or eq. (14) (newest secant exact)."""
    O = S.T @ Y
    m = O.shape[0]
    P = np.eye(H.shape[0]) - Y @ np.linalg.solve(O, S.T)  # P = I - Y O^{-1} S^T
    KR = polar_kernels(O)[0]
    Kinv = np.linalg.inv(KR)
    if exact_last:
        Omm = O[m - 1, m - 1]
        pi = np.eye(m) - np.outer(O[:, m - 1], np.eye(m)[m - 1]) / Omm  # pi = I - o_m e_m^T/O_mm
        Kinv = pi.T @ Kinv @ pi + np.outer(np.eye(m)[m - 1], np.eye(m)[m - 1]) / Omm  # eq. (14)
    return P.T @ H @ P + S @ Kinv @ S.T


def ms_bfgs_update_B(B, S, Y, exact_last=False):
    """Dense MS-BFGS direct update: eq. (10) (with K~_L of eq. (16) in the exact variant)."""
    O = S.T @ Y
    BS = B @ S
    KL = polar_kernels(O)[1]
    if exact_last:
        m = O.shape[0]
        ot = O[m - 1, :]
        pit = np.eye(m)
        pit[m - 1, :] -= ot / O[m - 1, m - 1]
        KL = pit.T @ KL @ pit + np.outer(ot, ot) / O[m - 1, m - 1]  # eq. (16)
    return B - BS @ np.linalg.solve(S.T @ BS, BS.T) + Y @ np.linalg.solve(KL, Y.T)


# ------------------------------------------------------------------------------------- window test
def _window_ok(O, StBS, YtHY, eps_s, eps_y, exact_last):
    """Inequalities (18)-(19) of [G26] for one candidate window (exact variant via (22), D7)."""
    if not all(np.all(np.isfinite(value)) for value in (O, StBS, YtHY)):
        return False
    try:
        U, sig, Vt = np.linalg.svd(O)
    except np.linalg.LinAlgError:
        return False
    if not (np.all(np.isfinite(sig)) and sig[-1] > 0.0):
        return False
    logdetK = float(np.sum(np.log(sig)))  # log det K_R
    trKLi = float(np.sum(1.0 / sig))  # tr K_L^{-1}
    if exact_last:
        mm = O.shape[0] - 1
        Omm = O[mm, mm]
        if not Omm > 0:
            return False
        KRmm = float(np.sum(U[mm, :] ** 2 * sig))  # (K_R)_mm
        logdetK += np.log(Omm) - np.log(KRmm)  # eq. (22): det K~_R = det K_R O_mm/(K_R)_mm
        trKLi += 1.0 / Omm  # literal upper bound of eq. (22)
    sign, logdetSBS = np.linalg.slogdet(0.5 * (StBS + StBS.T))
    if not sign > 0:
        return False
    if logdetK < np.log(eps_s) + logdetSBS:  # eq. (18)
        return False
    if 1.0 / trKLi < eps_y * float(np.trace(YtHY)):  # eq. (19)
        return False
    return True


def _select_window(Ofull, StBS, YtHY, M, eps_s, eps_y, exact_last):
    """Largest suffix window q <= M passing (18)-(19); drop oldest pairs on failure ([G26] Sec. 3).

    Returns q (>= 1) or 0 if even the single newest pair fails."""
    p = Ofull.shape[0]
    for q in range(min(max(M, 1), p), 0, -1):
        sl = slice(p - q, p)
        if _window_ok(Ofull[sl, sl], StBS[sl, sl], YtHY[sl, sl], eps_s, eps_y, exact_last):
            return q
    return 0


def gubarev_window(
    S, Y, H=None, B=None, eps_s=EPS_S, eps_y=EPS_Y, M=None, exact_last=False, O=None
):
    """Number of OLDEST pairs to drop by the window test of [G26] Sec. 3, eqs. (18)-(19).

    S, Y : n x p arrays, columns ordered oldest -> newest.
    H, B : callables applying the inverse Hessian / Hessian approximation BEFORE the update to an n x k
           array.  If None, each candidate window q is tested with the scalar H0 = gamma*_q I,
           B0 = I/gamma*_q of that window ([G26] Sec. 4.4), which makes the test scale invariant.
    M    : maximal window (default p).  exact_last: use the kernels of the exact-newest-secant variant (22).
    O    : optional precomputed overlap S^T Y (p x p), not symmetrized.
    Returns p - q for the largest passing suffix window q; if no window passes (not even the newest pair
    alone) returns p - 1: [G26] never drops the newest pair but damps it by (21) instead.
    """
    S = np.atleast_2d(np.asarray(S, dtype=float))
    Y = np.atleast_2d(np.asarray(Y, dtype=float))
    p = S.shape[1]
    if p == 0:
        return 0
    qmax = p if M is None else min(max(int(M), 1), p)
    Ofull = S.T @ Y if O is None else np.asarray(O, dtype=float)  # overlap O = S^T Y
    if H is not None and B is not None:
        Sc, Yc = S[:, p - qmax :], Y[:, p - qmax :]
        YtHY = Yc.T @ H(Yc)
        StBS = Sc.T @ B(Sc)
        q = _select_window(
            Ofull[p - qmax :, p - qmax :], StBS, YtHY, qmax, eps_s, eps_y, exact_last
        )
        return p - max(q, 1)
    SS, YY = S.T @ S, Y.T @ Y
    for q in range(qmax, 0, -1):
        sl = slice(p - q, p)
        Oq = Ofull[sl, sl]
        sig = np.linalg.svd(Oq, compute_uv=False)
        if not (np.all(np.isfinite(sig)) and sig[-1] > 0):
            continue
        gam = float(
            np.sum(sig) / np.trace(YY[sl, sl])
        )  # gamma* = tr K_R/||Y||_F^2 = ||r^{-1}O||_F^2/||Y||_F^2
        if _window_ok(Oq, SS[sl, sl] / gam, gam * YY[sl, sl], eps_s, eps_y, exact_last):
            return p - q
    return p - 1


# ------------------------------------------------------------------------------- damping (20)-(21)
def damping_thetas(p, q, c, eps_s=EPS_S, eps_y=EPS_Y, n_grid=91):
    """Solve min th_s^2 + th_y^2 s.t. (20) holds for the pair deformed by (21), 0 <= th <= 1/2.

    p = s^T B s, q = y^T H y, c = sign * s^T y (sign of (21)).  Returns (th_s, th_y) or None (D6).
    The deformed quantities (with H B = I):
      c' = c[(1-a)(1-b)+ab] + (1-a) b p + a(1-b) q,  p' = (1-a)^2 p + 2a(1-a) c + a^2 q,
      q' = (1-b)^2 q + 2b(1-b) c + b^2 p,   constraints c' >= eps_s p', c' >= eps_y q'.
    """
    # The constraints are homogeneous. Max scaling avoids overflow in p*q
    # even when both finite inputs are perfectly representable.
    sc = max(p, q, abs(c))
    if not (np.isfinite(sc) and sc > 0):
        return None
    p, q, c = p / sc, q / sc, c / sc
    tol = 1e-13 * (abs(c) + p + q)

    def cons(a, b):
        cc = c * ((1 - a) * (1 - b) + a * b) + (1 - a) * b * p + a * (1 - b) * q
        pp = (1 - a) ** 2 * p + 2 * a * (1 - a) * c + a * a * q
        qq = (1 - b) ** 2 * q + 2 * b * (1 - b) * c + b * b * p
        return cc - eps_s * pp, cc - eps_y * qq

    if min(cons(0.0, 0.0)) >= -tol:
        return 0.0, 0.0

    def rmin(phi):
        u = np.array([np.cos(phi), np.sin(phi)])
        rmax = 0.5 / max(u)
        # each constraint is an exact quadratic in r along the ray: fit through r = 0, rmax/2, rmax
        rs = np.array([0.0, 0.5 * rmax, rmax])
        vals = np.array([cons(*(r * u)) for r in rs])  # 3 x 2
        cands = [rmax]
        for j in range(2):
            co = np.polyfit(rs, vals[:, j], 2)
            for rt in np.roots(co) if np.any(co != 0) else []:
                if abs(rt.imag) < 1e-12 and 0.0 < rt.real <= rmax:
                    cands.append(float(rt.real))
        for r in sorted(cands):
            g1, g2 = cons(*(r * u))
            if g1 >= -tol and g2 >= -tol:
                return r
        return np.inf

    phis = np.linspace(0.0, 0.5 * np.pi, n_grid)
    rv = np.array([rmin(ph) for ph in phis])
    i = int(np.argmin(rv))
    if not np.isfinite(rv[i]):
        return None
    lo, hi = phis[max(i - 1, 0)], phis[min(i + 1, n_grid - 1)]
    best_phi, best_r = phis[i], rv[i]
    gr = 0.5 * (np.sqrt(5.0) - 1.0)  # golden-section refinement
    a, b = lo, hi
    x1, x2 = b - gr * (b - a), a + gr * (b - a)
    f1, f2 = rmin(x1), rmin(x2)
    for _ in range(40):
        if f1 < best_r:
            best_phi, best_r = x1, f1
        if f2 < best_r:
            best_phi, best_r = x2, f2
        if f1 <= f2:
            b, x2, f2 = x2, x1, f1
            x1 = b - gr * (b - a)
            f1 = rmin(x1)
        else:
            a, x1, f1 = x1, x2, f2
            x2 = a + gr * (b - a)
            f2 = rmin(x2)
    th = best_r * np.array([np.cos(best_phi), np.sin(best_phi)])
    th = np.clip(th, 0.0, 0.5)
    return float(th[0]), float(th[1])


# --------------------------------------------------------------------- limited-memory approximation
class MSLBFGSApprox:
    """Limited-memory MS-BFGS approximation ([G26] Sec. 4), compact form of D4.

    Stored pairs S, Y (n x p, oldest first, global ids first_id..first_id+p-1); updates = list of
    (lo_id, q, Ninv, C) = block update over pairs lo_id..lo_id+q-1 with kernel inverses for H and B.
    """

    def __init__(self, n, memory, M, exact_last=False, eps_s=EPS_S, eps_y=EPS_Y, positive=None):
        self.n = n
        self.memory = int(memory)
        self.M = min(int(M), self.memory)  # window <= memory ([G26] Sec. 4: M <= L)
        self.exact_last = bool(exact_last)
        self.eps_s = eps_s
        self.eps_y = eps_y
        # M = 0: single secant with curvature positivity (no modulus in (20)), [G26] Sec. 5
        self.positive = (self.M == 0 or self.exact_last) if positive is None else positive
        self.reset()

    def reset(self):
        n = self.n
        self.S = np.zeros((n, 0))
        self.Y = np.zeros((n, 0))
        self.first_id = 0
        self.next_id = 0
        self.updates = []
        self.update_roots = {}
        self.gamma = 1.0
        self.SS = np.zeros((0, 0))
        self.SY = np.zeros((0, 0))
        self.YY = np.zeros((0, 0))
        self.A = np.zeros((0, 0))
        self.N = np.zeros((0, 0))
        self.F = np.zeros((0, 0))
        self.basis = np.zeros((n, 0))
        self.h_chol = np.zeros((0, 0))
        self.m_hist = getattr(self, "m_hist", {})
        self.n_damped = getattr(self, "n_damped", 0)
        self.last_window = 0

    @property
    def trivial(self):
        return len(self.updates) == 0

    # ---------------------------------------------------------------- products
    def H(self, V):
        """Inverse Hessian approximation times V: gamma Q^T Q V + S N S^T V, Q = I - Y A S^T ((44), D4)."""
        if self.trivial:
            return self.gamma * V
        S, Y = self.S, self.Y
        StV = S.T @ V
        QV = V - Y @ (self.A @ StV)
        QtQV = QV - S @ (self.A.T @ (Y.T @ QV))
        return self.gamma * QtQV + S @ (self.F.T @ (self.F @ StV))

    def B(self, V):
        """Same Hessian as (10), obtained by inverting (44) on span(S,Y); no n x n matrix."""
        if self.trivial:
            return V / self.gamma
        z = self.basis.T @ V
        inverse_z = np.linalg.solve(self.h_chol.T, np.linalg.solve(self.h_chol, z))
        return (V - self.basis @ z) / self.gamma + self.basis @ inverse_z

    def _gram_H(self, V):
        if self.trivial:
            return self.gamma * (V.T @ V)
        stv = self.S.T @ V
        qv = V - self.Y @ (self.A @ stv)
        fv = self.F @ stv
        return self.gamma * (qv.T @ qv) + fv.T @ fv

    def _gram_B(self, V):
        if self.trivial:
            return (V.T @ V) / self.gamma
        z = self.basis.T @ V
        perp = V - self.basis @ z
        whitened = np.linalg.solve(self.h_chol, z)
        return (perp.T @ perp) / self.gamma + whitened.T @ whitened

    # ---------------------------------------------------------------- rebuild compact form
    def _rebuild(self):
        p = self.S.shape[1]
        I = np.eye(p)
        # Use the stored vectors consistently, rather than cached dot products
        # that may disagree with the overlap used for the accepted kernel.
        SY = self.S.T @ self.Y
        A = np.zeros((p, p))
        F = np.zeros((0, p))
        for lo, q, Ninv, C in self.updates:
            w = np.arange(lo - self.first_id, lo - self.first_id + q)
            O = SY[np.ix_(w, w)]  # O = S_w^T Y_w
            OiEt = np.linalg.solve(O, I[w, :])  # O^{-1} E^T
            # H side: Q <- Q P_w,  P_w = I - Y_w O^{-1} S_w^T  (projector products, Sec. 4.2, (24)-(30))
            A = A + (I - A @ SY)[:, w] @ OiEt
            T = I - SY[:, w] @ OiEt  # S^T P_w = T S^T
            F = F @ T  # factor version of N <- T^T N T
            kernel_root = self.update_roots[lo, q]
            newest = np.zeros((kernel_root.shape[0], p))
            newest[:, w] = kernel_root
            F = np.concatenate([F, newest], axis=0)
        if not (np.all(np.isfinite(A)) and np.all(np.isfinite(F))):
            raise np.linalg.LinAlgError("non-finite compact factors")
        self.A, self.F, self.N = A, F, F.T @ F
        U = np.concatenate([self.S, self.Y], axis=1)
        scales = np.max(np.abs(U), axis=0)
        if not np.all(np.isfinite(scales)) or np.any(scales == 0):
            raise np.linalg.LinAlgError("non-finite or zero compact column")
        # Retain every QR column: there is no tolerance, discarded singular
        # value, ridge or pseudo-inverse. Extra dependent-column directions
        # simply carry the scalar H0, as on the orthogonal complement.
        basis = np.linalg.qr(U / scales, mode="reduced")[0]
        stv = self.S.T @ basis
        qv = basis - self.Y @ (self.A @ stv)
        features = np.vstack([np.sqrt(self.gamma) * qv, self.F @ stv])
        if not np.all(np.isfinite(features)):
            raise np.linalg.LinAlgError("non-finite reduced Hessian factors")
        # Hr = features.T @ features. Factoring Hr itself squares the condition
        # and lost positivity on PENALTY2. QR retains the identical matrix's
        # factor without that Gram formation, rank cut or diagonal shift.
        self.h_chol = np.linalg.qr(features, mode="reduced")[1].T
        self.basis = basis

    def _append_pair(self, s, y):
        S, Y = self.S, self.Y
        Sts, Sty, Yts, Yty = S.T @ s, S.T @ y, Y.T @ s, Y.T @ y
        ss, sy, yy = float(s @ s), float(s @ y), float(y @ y)
        self.SS = np.block([[self.SS, Sts[:, None]], [Sts[None, :], np.array([[ss]])]])
        self.YY = np.block([[self.YY, Yty[:, None]], [Yty[None, :], np.array([[yy]])]])
        self.SY = np.block([[self.SY, Sty[:, None]], [Yts[None, :], np.array([[sy]])]])
        self.S = np.concatenate([S, s[:, None]], axis=1)
        self.Y = np.concatenate([Y, y[:, None]], axis=1)
        self.next_id += 1

    def _truncate(self):
        """Keep the newest `memory` pairs and the longest suffix of updates inside them (D3, Fig. 1)."""
        p = self.S.shape[1]
        if p > self.memory:
            k = p - self.memory
            self.S, self.Y = self.S[:, k:], self.Y[:, k:]
            self.SS, self.SY, self.YY = self.SS[k:, k:], self.SY[k:, k:], self.YY[k:, k:]
            self.first_id += k
        keep = []
        for up in reversed(self.updates):
            if up[0] < self.first_id:
                break
            keep.append(up)
        self.updates = keep[::-1]
        self.update_roots = {(lo, q): self.update_roots[lo, q] for lo, q, _, _ in self.updates}

    # ---------------------------------------------------------------- the update
    def update(self, s, y):
        """Process the new pair: window selection (18)-(19), damping (20)-(21), block update (9)/(14)."""
        p_old = self.S.shape[1]
        qmax = min(max(self.M, 1), p_old + 1)
        Sc = np.concatenate([self.S[:, p_old - (qmax - 1) :], s[:, None]], axis=1)
        Yc = np.concatenate([self.Y[:, p_old - (qmax - 1) :], y[:, None]], axis=1)
        if self.trivial:  # D5
            yy = float(y @ y)
            if not (yy > 0 and abs(float(s @ y)) > 0):
                gam = self.gamma
            else:
                gam = abs(float(s @ y)) / yy
            HY, BS = gam * Yc, Sc / gam
        else:
            HY, BS = self.H(Yc), self.B(Sc)  # B, H before the update
        YtHY = Yc.T @ HY if self.trivial else self._gram_H(Yc)
        StBS = Sc.T @ BS if self.trivial else self._gram_B(Sc)
        Ofull = Sc.T @ Yc
        es, ey = self.eps_s, self.eps_y

        def damp_newest(sign):
            """Symmetric damping (21) of the newest pair so that (20) holds; updates Sc, Yc, Grams."""
            pB, qH, c = StBS[-1, -1], YtHY[-1, -1], sign * Ofull[-1, -1]
            th = damping_thetas(pB, qH, c, es, ey)
            if th is None:
                return False
            ts, ty = th
            if ts == 0.0 and ty == 0.0:
                return True
            s_new = (1 - ts) * Sc[:, -1] + sign * ts * HY[:, -1]  # eq. (21)
            y_new = (1 - ty) * Yc[:, -1] + sign * ty * BS[:, -1]  # eq. (21)
            hy_new = (1 - ty) * HY[:, -1] + sign * ty * Sc[:, -1]  # H y' (H B = I)
            bs_new = (1 - ts) * BS[:, -1] + sign * ts * Yc[:, -1]  # B s'
            Sc[:, -1], Yc[:, -1], HY[:, -1], BS[:, -1] = s_new, y_new, hy_new, bs_new
            YtHY[:, :] = Yc.T @ HY if self.trivial else self._gram_H(Yc)
            StBS[:, :] = Sc.T @ BS if self.trivial else self._gram_B(Sc)
            Ofull[:, :] = Sc.T @ Yc
            self.n_damped += 1
            return True

        if self.positive:
            # (20) without modulus, positive sign: M = 0, and first step of the exact variant (Sec. 3 end)
            c = Ofull[-1, -1]
            if not (c >= max(es * StBS[-1, -1], ey * YtHY[-1, -1]) and c > 0):
                if not damp_newest(1.0):
                    return False
        if self.M == 0:
            q = 1
        else:
            q = _select_window(Ofull, StBS, YtHY, self.M, es, ey, self.exact_last)  # (18)-(19)
            if q == 0:
                q = 1
                if not self.positive:
                    sign = 1.0 if Ofull[-1, -1] >= 0 else -1.0  # sign in (21)
                    if not damp_newest(sign):
                        return False
        # kernels of the accepted window; fall back to smaller windows if a factorization fails
        while True:
            sl = slice(qmax - q, qmax)
            O = Ofull[sl, sl]
            try:
                Ninv, C, rR, kernel_root = _kernels(O, self.exact_last, return_root=True)
                gam = _gamma_star(O, Yc[:, sl], rR)  # Sec. 4.4
                if not (
                    np.isfinite(gam)
                    and gam > 0
                    and np.all(np.isfinite(Ninv))
                    and np.all(np.isfinite(C))
                ):
                    raise np.linalg.LinAlgError("non-finite kernel")
                break
            except np.linalg.LinAlgError:
                if q == 1:
                    return False  # D6: skip the pair
                # A smaller suffix need not pass the same inequalities. Apply
                # the author's window test again, then (20)-(21) at q = 1.
                q = _select_window(Ofull, StBS, YtHY, q - 1, es, ey, self.exact_last)
                if q == 0:
                    q = 1
                    if not self.positive:
                        sign = 1.0 if Ofull[-1, -1] >= 0 else -1.0
                        if not damp_newest(sign):
                            return False
        self._append_pair(Sc[:, -1].copy(), Yc[:, -1].copy())
        new_id = self.next_id - 1
        self.updates.append((new_id - q + 1, q, Ninv, C))
        self.update_roots[new_id - q + 1, q] = kernel_root
        self.gamma = gam
        self._truncate()
        self._rebuild()
        self.m_hist[q] = self.m_hist.get(q, 0) + 1
        self.last_window = q
        return True


# ------------------------------------------------------------------------------------- line searches
def _armijo(O, x, f, g, d, c1=1e-4, alpha=1.0, max_back=100):
    """Armijo acceptance from the unit step with guarded quadratic backtracking ([G26] Sec. 5; D1)."""
    gtd = float(g @ d)
    if not (np.isfinite(gtd) and gtd < 0):
        return None
    for _ in range(max_back):
        xn = x + alpha * d
        if np.array_equal(xn, x):
            return None
        fn = O.f(xn)
        if not np.isfinite(fn):
            alpha *= 0.1  # backtracking safeguard on non-finite values
            continue
        if fn <= f + c1 * alpha * gtd:  # Armijo
            return xn, fn
        den = 2.0 * (fn - f - alpha * gtd)
        at = -gtd * alpha * alpha / den if den > 0 else 0.5 * alpha
        alpha = min(max(at, 0.1 * alpha), 0.5 * alpha)  # guarded quadratic guess
    return None


def _goldstein(O, x, f, g, d, c=0.25, alpha=1.0, max_trials=100):
    """Goldstein rules f + (1-c) a g^T d <= f(x + a d) <= f + c a g^T d ([G26] Sec. 5; D1)."""
    gtd = float(g @ d)
    if not (np.isfinite(gtd) and gtd < 0):
        return None
    lo, hi = 0.0, np.inf
    best = None
    for _ in range(max_trials):
        xn = x + alpha * d
        if np.array_equal(xn, x):
            break
        fn = O.f(xn)
        if not np.isfinite(fn):
            hi = alpha
            alpha = 0.5 * (lo + hi) if lo > 0 else 0.1 * alpha
            continue
        if fn > f + c * alpha * gtd:  # too long
            hi = alpha
            if lo > 0:
                alpha = 0.5 * (lo + hi)
            else:
                den = 2.0 * (fn - f - alpha * gtd)
                at = -gtd * alpha * alpha / den if den > 0 else 0.5 * alpha
                alpha = min(max(at, 0.1 * alpha), 0.5 * alpha)
            continue
        if fn < f + (1.0 - c) * alpha * gtd:  # too short (sufficient decrease holds)
            lo = alpha
            if best is None or fn < best[1]:
                best = (xn, fn)
            if np.isfinite(hi):
                alpha = 0.5 * (lo + hi)
            else:
                den = 2.0 * (fn - f - alpha * gtd)
                at = -gtd * alpha * alpha / den if den > 0 else 10.0 * alpha
                alpha = min(max(at, 2.0 * alpha), 10.0 * alpha)
            continue
        return xn, fn
    return best


# --------------------------------------------------------------------------------------- the solver
def solve(
    O, x0, m=8, M=8, exact_last=False, eps_s=EPS_S, eps_y=EPS_Y, c1=1e-4, c_gold=0.25, callback=None
):
    """MS-L-BFGS of [G26].  m = memory (paper's L), M = max secants per update (paper's M; M = 0 is the
    positivity-enforcing single-secant variant), exact_last = newest secant exact (paper's M*)."""
    x = np.array(x0, dtype=float)
    f, g = O.fg(x)
    ap = MSLBFGSApprox(x.size, m, M, exact_last, eps_s, eps_y)
    while True:
        if ap.trivial:
            gn = float(np.linalg.norm(g))
            if not (np.isfinite(gn) and gn > 0):
                O.note("stop", "zero_gradient" if gn == 0 else "nonfinite")
                return x
            res = _goldstein(O, x, f, g, -g, c_gold, 1.0 / gn)  # first iteration / after reset
        else:
            d = -ap.H(g)
            res = _armijo(O, x, f, g, d, c1, 1.0)  # unit initial step
        if res is None:
            if ap.trivial:
                O.note("stop", "line_search_failed_after_reset")
                return x  # D2
            ap.reset()  # reset on failed line search
            continue
        xn, fn = res
        gnew = O.g(xn)
        O.mark_iter()
        try:
            ap.update(xn - x, gnew - g)
        except np.linalg.LinAlgError as ex:
            # The update is undefined at working precision. Do not turn a
            # failed factorization into a different matrix or a convergence.
            O.note("stop", "numerical_failure")
            O.note("detail", str(ex))
            return xn
        x, f, g = xn, fn, gnew
        if callback is not None:
            callback(ap, x)
