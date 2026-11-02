"""Independent exact history from the polynomial basis (no short recurrence).

Use the constructive converse of the Bezoutian identity: expand
(1-q_s)/lambda in earlier q_j and (1-p_N)/lambda in the whole basis.
This intentionally uses dense history and Fraction arithmetic only in tests.
"""

from fractions import Fraction as F


def add(a, b):
    return [
        (a[j] if j < len(a) else F(0)) + (b[j] if j < len(b) else F(0))
        for j in range(max(len(a), len(b)))
    ]


def scale(a, c):
    return [c * v for v in a]


def multiply(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def value(p, x):
    out = F(0)
    for v in reversed(p):
        out = out * x + v
    return out


def expand(p, basis):
    remainder = list(p) + [F(0)] * max(0, len(basis) - len(p))
    out = [F(0)] * len(basis)
    for j in reversed(range(len(basis))):
        out[j] = remainder[j] / basis[j][j]
        for k, v in enumerate(basis[j]):
            remainder[k] -= out[j] * v
    assert all(v == 0 for v in remainder)
    return out


def run(name, N, mu, L, lam, tape, x0, star):
    delta = L - mu
    eta = (L + mu) / delta
    z = [eta, -2 / delta]
    T = [[F(1)], z]
    U = [[F(1)], scale(z, F(2))]
    for s in range(2, N + 1):
        T.append(add(scale(multiply(z, T[-1]), F(2)), scale(T[-2], F(-1))))
        U.append(add(scale(multiply(z, U[-1]), F(2)), scale(U[-2], F(-1))))
    C = [p[0] for p in T]
    u = [p[0] for p in U]
    if name == "flat":
        mass = [u[N - 1] / 2] + [u[N - 1 - j] for j in range(1, N)]
        d = sum(mass) / N
        R = [sum(mass[: m + 1]) - m * d for m in range(N)]
        tau = [R[N - 1 - s] / d - 1 for s in range(N)]
        q = []
        for s in range(N):
            p = scale(U[s], (1 + tau[s]) / u[s])
            if s:
                p = add(p, scale(U[s - 1], -tau[s] / u[s - 1]))
            q.append(p)
    else:
        psi = [T[0], T[1]]
        for s in range(2, N):
            w = (
                F(N + 2 - s - s % 2, N)
                if N % 2 == 0
                else F((N + 1) * (N + 1 - s), N * N + 1)
                if s % 2 == 0
                else F(N + 2 - s, N + 1)
            )
            psi.append(add(psi[s - 2], scale(add(T[s], scale(T[s - 2], F(-1))), w)))
        q = [scale(p, 1 / p[0]) for p in psi[:N]]
    p = scale(T[N], 1 / C[N])
    A = [expand(scale(v[1:], F(-1)), q[:s]) for s, v in enumerate(q)]
    b = expand(scale(p[1:], F(-1)), q)
    initial = x0 - star
    answers = []
    queries = []
    for s in range(N):
        query = initial - sum(a * g for a, g in zip(A[s], answers))
        queries.append(star + query)
        answers.append(lam * query + tape[s])
    return star + initial - sum(a * g for a, g in zip(b, answers)), queries
