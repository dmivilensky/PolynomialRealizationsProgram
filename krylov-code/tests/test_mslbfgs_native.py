"""Native MS-L-BFGS: paper identities, reference differential, full C loop.

The diagnostic API is called directly through ctypes so the tested products
are exactly those used by the native optimizer; no Python model drives C.
"""

import ctypes as ct
import hashlib
import os
import subprocess
import tempfile
from pathlib import Path

import numpy as np
import pytest
from scipy.linalg import cython_blas, cython_lapack

from xrbench.methods import mslbfgs as ms
from xrbench.oracle import Oracle, run_method

P = ct.POINTER(ct.c_double)
I = ct.POINTER(ct.c_int)


@pytest.fixture(scope="module")
def native():
    directory = Path(__file__).resolve().parents[1] / "src/xrbench/native"
    files = [
        directory / s
        for s in (
            "mslbfgs_native.c",
            "competitor_common.c",
            "competitor_common.h",
            "mslbfgs_native.h",
            "xr_native.h",
        )
    ]
    key = hashlib.sha256(b"".join(p.read_bytes() for p in files)).hexdigest()
    folder = Path(tempfile.gettempdir()) / "clc-xr-ms-tests" / key
    folder.mkdir(parents=True, exist_ok=True)
    so = folder / "ms.so"
    if not so.exists():
        command = [
            "cc",
            "-shared",
            "-O3",
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-fno-fast-math",
            "-ffp-contract=off",
        ]
        if os.uname().sysname == "Darwin":
            command += [
                "-isysroot",
                subprocess.check_output(["xcrun", "--show-sdk-path"], text=True).strip(),
            ]
        command += [str(files[0]), str(files[1]), "-o", str(so)]
        subprocess.run(command, check=True, capture_output=True)
    lib = ct.CDLL(str(so))
    getname = ct.pythonapi.PyCapsule_GetName
    getname.restype = ct.c_char_p
    getname.argtypes = [ct.py_object]
    getpointer = ct.pythonapi.PyCapsule_GetPointer
    getpointer.restype = ct.c_void_p
    getpointer.argtypes = [ct.py_object, ct.c_char_p]
    symbols = [
        "ddot",
        "dnrm2",
        "dgemv",
        "dgemm",
        "dpotrf",
        "dpotrs",
        "dgesv",
        "dtrcon",
        "dsyev",
        "dtrsm",
        "zpotrf",
        None,
        None,
        "dgeqrf",
        "dorgqr",
        "dgeqp3",
        "dgesvd",
    ]
    backend = (ct.c_void_p * len(symbols))()
    for i, symbol in enumerate(symbols):
        if symbol:
            capsules = (
                cython_blas.__pyx_capi__
                if symbol in ("ddot", "dnrm2", "dgemv", "dgemm", "dtrsm")
                else cython_lapack.__pyx_capi__
            )
            capsule = capsules[symbol]
            backend[i] = getpointer(capsule, getname(capsule))
    lib.cn_ms_create.argtypes = [
        ct.c_int,
        ct.c_int,
        ct.c_int,
        ct.c_double,
        ct.c_double,
        ct.c_void_p,
    ]
    lib.cn_ms_create.restype = ct.c_void_p
    lib.cn_ms_destroy.argtypes = [ct.c_void_p]
    lib.cn_ms_update.argtypes = [ct.c_void_p, P, P]
    lib.cn_ms_product.argtypes = [ct.c_void_p, P, P, ct.c_int]
    lib.cn_ms_snapshot.argtypes = [ct.c_void_p, P, P, I, P]
    lib.cn_ms_damping.argtypes = [ct.c_double] * 5 + [P, P]
    return lib, backend


def ptr(a):
    return a.ctypes.data_as(P)


class Model:
    def __init__(self, native, n, memory, M):
        self.lib, self.backend = native
        self.n, self.memory = n, memory
        self.handle = self.lib.cn_ms_create(n, memory, M, 0.01, 0.001, self.backend)
        assert self.handle

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.lib.cn_ms_destroy(self.handle)

    def update(self, s, y):
        return self.lib.cn_ms_update(
            self.handle, ptr(np.ascontiguousarray(s)), ptr(np.ascontiguousarray(y))
        )

    def product(self, v, inverse=True):
        v = np.ascontiguousarray(v)
        out = np.zeros_like(v)
        assert self.lib.cn_ms_product(self.handle, ptr(v), ptr(out), int(inverse))
        return out

    def snapshot(self):
        S = np.zeros((self.n, self.memory), order="F")
        Y = np.zeros_like(S, order="F")
        info = np.zeros(4, dtype=np.int32)
        gamma = np.zeros(1)
        self.lib.cn_ms_snapshot(self.handle, ptr(S), ptr(Y), info.ctypes.data_as(I), ptr(gamma))
        return S[:, : info[0]], Y[:, : info[0]], info, gamma[0]


@pytest.mark.parametrize("n,m,M", [(20, 8, 8), (10, 6, 3), (12, 5, 1), (4, 8, 8), (15, 8, 0)])
def test_native_model_matches_independent_dense_and_reference(native, n, m, M):
    rng = np.random.default_rng(422 + M)
    Q = np.linalg.qr(rng.normal(size=(n, n)))[0]
    A = (Q * np.geomspace(1, 30, n)) @ Q.T
    ap = ms.MSLBFGSApprox(n, m, M)
    with Model(native, n, m, M) as model:
        for _ in range(18):
            s = rng.normal(size=n)
            y = A @ s + 0.2 * rng.normal(size=n)
            assert ap.update(s, y)
            assert model.update(s, y) == 1
            S, Y, info, gamma = model.snapshot()
            np.testing.assert_allclose(S, ap.S, rtol=2e-9, atol=1e-10)
            np.testing.assert_allclose(Y, ap.Y, rtol=2e-9, atol=1e-10)
            assert info[1] == len(ap.updates)
            assert info[2] == ap.last_window
            assert gamma == pytest.approx(ap.gamma, rel=2e-10)
            # Independent literal block recursion (9) with NumPy SVD kernel.
            H = gamma * np.eye(n)
            for lo, q, _, _ in ap.updates:
                w = slice(lo - ap.first_id, lo - ap.first_id + q)
                Sw, Yw = S[:, w], Y[:, w]
                O = Sw.T @ Yw
                U, sig, _ = np.linalg.svd(O)
                Pj = np.eye(n) - Yw @ np.linalg.solve(O, Sw.T)
                H = Pj.T @ H @ Pj + (Sw @ (U / sig)) @ (Sw @ U).T
            Hn = np.column_stack([model.product(e) for e in np.eye(n)])
            Bn = np.column_stack([model.product(e, False) for e in np.eye(n)])
            np.testing.assert_allclose(Hn, H, rtol=2e-8, atol=2e-9)
            np.testing.assert_allclose(Bn @ Hn, np.eye(n), rtol=2e-8, atol=2e-8)


@pytest.mark.parametrize("sign", [-1, 1])
def test_native_damping_feasible_and_minimal(native, sign):
    lib, _ = native
    rng = np.random.default_rng(88)
    grid = np.linspace(0, 0.5, 151)
    agrid, bgrid = np.meshgrid(grid, grid)
    for _ in range(30):
        p, q = np.exp(rng.uniform(-6, 6, 2))
        c = sign * 0.001 * np.sqrt(p * q)
        a, b = ct.c_double(), ct.c_double()
        assert lib.cn_ms_damping(p, q, c, 0.01, 0.001, ct.byref(a), ct.byref(b))
        th = ms.damping_thetas(p, q, c)
        np.testing.assert_allclose([a.value, b.value], th, atol=2e-6)

        def feasible(a, b):
            cc = c * ((1 - a) * (1 - b) + a * b) + (1 - a) * b * p + a * (1 - b) * q
            pp = (1 - a) ** 2 * p + 2 * a * (1 - a) * c + a * a * q
            qq = (1 - b) ** 2 * q + 2 * b * (1 - b) * c + b * b * p
            return (cc >= 0.01 * pp - 1e-11 * (p + q)) & (cc >= 0.001 * qq - 1e-11 * (p + q))

        assert feasible(a.value, b.value)
        feasible_grid = feasible(agrid, bgrid)
        assert a.value**2 + b.value**2 <= np.min((agrid**2 + bgrid**2)[feasible_grid]) + 1e-7


def test_native_negative_curvature_uniform_and_positive_variants(native):
    rng = np.random.default_rng(19)
    s = rng.normal(size=12)
    y = -s + 1e-5 * rng.normal(size=12)
    with Model(native, 12, 8, 8) as model:
        assert model.update(s, y) == 1
        assert s @ model.product(y) < 0  # polar sign-blind secant
    with Model(native, 12, 8, 0) as model:
        assert model.update(s, y) == 1
        S, Y, info, _ = model.snapshot()
        assert S[:, -1] @ Y[:, -1] > 0
        assert info[3] == 1


FG = ct.CFUNCTYPE(ct.c_int, ct.c_void_p, P, P, P)
FC = ct.CFUNCTYPE(ct.c_int, ct.c_void_p, P, P)
GC = ct.CFUNCTYPE(ct.c_int, ct.c_void_p, P, P)
MARK = ct.CFUNCTYPE(ct.c_int, ct.c_void_p)
NOTE = ct.CFUNCTYPE(ct.c_int, ct.c_void_p, ct.c_char_p, ct.c_double)
STOP = ct.CFUNCTYPE(ct.c_int, ct.c_void_p, ct.c_char_p)


class NativeOracle(ct.Structure):
    _fields_ = [
        ("n", ct.c_int),
        ("context", ct.c_void_p),
        ("fg", FG),
        ("f", FC),
        ("g", GC),
        ("mark", MARK),
        ("note", NOTE),
        ("stop", STOP),
        ("trace", ct.c_void_p),
    ]


class Params(ct.Structure):
    _fields_ = [("items", ct.c_void_p), ("count", ct.c_int)]


def native_solve(native, oracle, x0):
    lib, backend = native
    errors = []
    n = len(x0)

    def wrap(fun):
        def call(*args):
            try:
                fun(*args)
                return 0
            except BaseException as exc:
                errors.append(exc)
                return 1

        return call

    def view(p):
        return np.ctypeslib.as_array(p, shape=(n,))

    def fg(_, x, f, g):
        f[0], value = oracle.fg(view(x))
        view(g)[:] = value

    def fc(_, x, f):
        f[0] = oracle.f(view(x))

    def gc(_, x, g):
        view(g)[:] = oracle.g(view(x))

    api = NativeOracle(
        n,
        None,
        FG(wrap(fg)),
        FC(wrap(fc)),
        GC(wrap(gc)),
        MARK(wrap(lambda _: oracle.mark_iter())),
        NOTE(wrap(lambda _, k, v: oracle.note(k.decode(), v))),
        STOP(wrap(lambda _, s: oracle.note("stop", s.decode()))),
        None,
    )
    params = Params(None, 0)
    lib.cn_ms_execute.argtypes = [ct.POINTER(Params), ct.c_void_p, ct.POINTER(NativeOracle), P]
    rc = lib.cn_ms_execute(ct.byref(params), backend, ct.byref(api), ptr(np.ascontiguousarray(x0)))
    if errors:
        raise errors[0]
    assert rc == 0


@pytest.mark.parametrize("kind", ["quadratic", "rosenbrock"])
def test_complete_native_optimizer_converges_and_matches_early_queries(native, kind):
    from test_mslbfgs import Quad, Rosenbrock

    problem = Quad(20, 1e3) if kind == "quadratic" else Rosenbrock(10)

    class Recording(Oracle):
        def __init__(self):
            super().__init__(problem, budget=5000, gtol=1e-7)
            self.points = []

        def g(self, x):
            if len(self.points) < 8:
                self.points.append(np.copy(x))
            return super().g(x)

    refs = []
    for solve in (ms.solve, lambda O, x: native_solve(native, O, x)):
        result = run_method(solve, problem, problem.x0, {}, budget=5000, gtol=1e-7)
        assert result["status"] == "converged", result
        oracle = Recording()
        try:
            solve(oracle, problem.x0)
        except Exception:
            pass
        refs.append(oracle.points)
    np.testing.assert_allclose(refs[0], refs[1], rtol=1e-8, atol=1e-9)


def test_zero_pair_is_skipped_without_changing_model(native):
    with Model(native, 7, 8, 8) as model:
        zero = np.zeros(7)
        assert model.update(zero, zero) == 0
        v = np.arange(7, dtype=float)
        np.testing.assert_array_equal(model.product(v), v)
        assert model.snapshot()[2][1] == 0


def test_positive_damping_model_agrees_with_reference(native):
    rng = np.random.default_rng(215)
    ap = ms.MSLBFGSApprox(10, 8, 0)
    with Model(native, 10, 8, 0) as model:
        for _ in range(10):
            s = rng.normal(size=10)
            y = -0.15 * s + rng.normal(size=10)
            assert model.update(s, y) == 1
            assert ap.update(s, y)
            S, Y, info, gamma = model.snapshot()
            np.testing.assert_allclose(S, ap.S, rtol=3e-6, atol=1e-6)
            np.testing.assert_allclose(Y, ap.Y, rtol=3e-6, atol=1e-6)
            assert gamma == pytest.approx(ap.gamma, rel=3e-6)
            assert info[3] == ap.n_damped


def test_callback_exception_is_preserved(native):
    class StopNow:
        def fg(self, _):
            raise RuntimeError("exact sentinel from oracle")

    with pytest.raises(RuntimeError, match="exact sentinel from oracle"):
        native_solve(native, StopNow(), np.zeros(10))


@pytest.mark.parametrize("kind", ["quadratic", "rosenbrock"])
def test_integrated_native_bridge_optimizer_and_trace(kind):
    from test_mslbfgs import Quad, Rosenbrock

    from xrbench.methods.competitors_native import solve

    problem = Quad(20, 1e3) if kind == "quadratic" else Rosenbrock(10)
    events = []
    result = run_method(
        solve,
        problem,
        problem.x0,
        dict(native_method="mslbfgs", trace=events),
        budget=5000,
        gtol=1e-7,
    )
    assert result["status"] == "converged", result
    assert events
    assert all(event["kind"] == "accepted" for event in events)
    assert max(event["window"] for event in events) > 1


def test_integrated_native_bridge_budget_exception_is_not_swallowed():
    from test_mslbfgs import Quad

    from xrbench.methods.competitors_native import solve

    problem = Quad(20, 1e3)
    result = run_method(
        solve, problem, problem.x0, dict(native_method="mslbfgs"), budget=2, gtol=1e-20
    )
    assert result["status"] == "budget", result


def test_production_optimizer_rejects_unused_positive_pair_variant():
    from xrbench.methods.competitors_native import solve

    class NoCalls:
        def fg(self, _):
            raise AssertionError("Unsupported variant must be rejected before its oracle")

    with pytest.raises(ValueError):
        solve(NoCalls(), np.zeros(4), native_method="mslbfgs", M=0)
