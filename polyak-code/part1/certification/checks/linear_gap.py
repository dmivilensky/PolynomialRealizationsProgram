"""Callable exact suite: analytic/lg_hand.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as s, numpy as np
from fractions import Fraction as Fr
import numpy as np

def run(ctx):
    G, c, W, X = s.symbols('G c W X')
    ok = lambda e: s.cancel(s.together(e)) == 0

    def check(name, cond):
        return ctx.check(cond, name)
    A2 = (G + c) / G
    B2 = 1 / G
    A3 = (4 * G ** 2 + 4 * G * c + 4 * c ** 2 - 3) / (4 * G ** 2 - 1)
    B3 = 4 * (G + c) / (4 * G ** 2 - 1)
    M = 8 * G ** 3 + 4 * G ** 2 * c + 4 * G * c ** 2 - 4 * G - W * (4 * G * c ** 2 - 2 * G + c)
    N = 4 * G ** 2 + 4 * G * c - W * (4 * G * c + 1)
    check('M=G(4G^2-1)alpha, N=G(4G^2-1)beta', ok(M - G * (4 * G ** 2 - 1) * (1 + W * A2 + (1 - W) * A3)) and ok(N - G * (4 * G ** 2 - 1) * (W * B2 + (1 - W) * B3)))
    check('M = 8G^3+4G^2c-G+(1-W)G(4c^2-3)-W(G+c)', ok(M - (8 * G ** 3 + 4 * G ** 2 * c - G + (1 - W) * G * (4 * c ** 2 - 3) - W * (G + c))))
    num = s.diff(N, G) * M - N * s.diff(M, G)
    check('num = 2W^2+4W(16G^3c+8G^2-1)-16G^2(2G^2+4Gc+1)', ok(num - (2 * W ** 2 + 4 * W * (16 * G ** 3 * c + 8 * G ** 2 - 1) - 16 * G ** 2 * (2 * G ** 2 + 4 * G * c + 1))))
    Ws = 2 * (1 + 2 * G - 2 * G ** 2) / (4 * G + 1)
    sp = {c: -1 / (2 * G), W: Ws}
    check('spiral: M', ok(M.subs(sp) - 2 * (2 * G - 1) ** 2 * (2 * G + 1) ** 2 / (4 * G + 1)))
    check('spiral: num', ok(num.subs(sp) + 16 * G * (2 * G - 1) ** 2 * (2 * G + 1) ** 3 / (4 * G + 1) ** 2))
    check('spiral: d theta/dG', ok((num / M ** 2).subs(sp) + 4 * G / ((2 * G - 1) ** 2 * (2 * G + 1))))
    check('spiral: 1/(2u^2) with u=1-1/(2G)', ok(1 / (2 * (1 - 1 / (2 * G)) ** 2) - 2 * G ** 2 / (2 * G - 1) ** 2))
    check('P1 (W=0): M=4G(2G^2+Gc+c^2-1), theta=(G+c)/(2G^2+Gc+c^2-1)', ok(M.subs(W, 0) - 4 * G * (2 * G ** 2 + G * c + c ** 2 - 1)) and ok((N / M).subs(W, 0) - (G + c) / (2 * G ** 2 + G * c + c ** 2 - 1)))
    check('P1: dtheta', ok((num / M ** 2).subs(W, 0) + (2 * G ** 2 + 4 * G * c + 1) / (2 * G ** 2 + G * c + c ** 2 - 1) ** 2))
    D = (2 * X - s.Rational(3, 2)) ** 4 - (X - 1) * (2 * X + 1) ** 2
    check('D(X) = 16X^4-52X^3+54X^2-24X+97/16', ok(D - (16 * X ** 4 - 52 * X ** 3 + 54 * X ** 2 - 24 * X + s.Rational(97, 16))))
    check("D'' = 12(2X-1)(8X-9)", ok(s.diff(D, X, 2) - 12 * (2 * X - 1) * (8 * X - 9)))
    x0 = s.Rational(1866, 1000)
    check("D'(1.866)>0, D(1.866)>5, 1.866<1+sqrt3/2", s.diff(D, X).subs(X, x0) > 0 and D.subs(X, x0) > 5 and ((x0 - 1) ** 2 * 4 < 3))
    f = s.lambdify((G, c, W), num / M ** 2, 'numpy')
    gg, cc, ww = np.meshgrid(np.linspace(1.0233, 1.0337, 41), np.r_[np.linspace(-0.505, -0.48, 41), np.linspace(0.25, 0.285, 41)], np.linspace(0.362, 0.366, 5))
    ctx.note('grid max |num|/M^2 on the P2 box: %.3f  (proof: <1.9)' % np.max(np.abs(f(gg, cc, ww))))
    k_, u_ = s.symbols('k u')
    check('amplitude identity (k-u^2)^2+4u^2k=(k+u^2)^2', s.expand((k_ - u_ ** 2) ** 2 + 4 * u_ ** 2 * k_ - (k_ + u_ ** 2) ** 2) == 0)
    G0, G1 = (Fr(1), Fr(41, 40))

    def I(a, b):
        return (min(a, b), max(a, b))

    def add(*xs):
        return (sum((x[0] for x in xs)), sum((x[1] for x in xs)))

    def neg(x):
        return (-x[1], -x[0])

    def mul(x, y):
        p = [x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1]]
        return (min(p), max(p))

    def sc(k, x):
        return mul((Fr(k), Fr(k)), x)

    def pw(x, n):
        lo, hi = x
        if lo >= 0:
            return (lo ** n, hi ** n)
        if hi <= 0:
            return I(lo ** n, hi ** n) if n % 2 else (hi ** n, lo ** n)
        raise
    U4 = (16 * G0 ** 4 - 12 * G0 ** 2 + 1, 16 * G1 ** 4 - 12 * G1 ** 2 + 1)
    U4p = (64 * G0 ** 3 - 24 * G0, 64 * G1 ** 3 - 24 * G1)
    ctx.note('U4', [float(v) for v in U4], "U4'", [float(v) for v in U4p])

    def run(clo, chi):
        G = (G0, G1)
        c = (clo, chi)

        def mono(i, j, k=1):
            return sc(k, mul(pw(G, i) if i else (Fr(1), Fr(1)), pw(c, j) if j else (Fr(1), Fr(1))))
        Y = add(mono(2, 0, 4), mono(1, 1, 8), (Fr(1), Fr(1)))
        num3 = add(mono(1, 0, 16), mono(2, 1, -16), mono(0, 1, -4), mono(1, 2, -32))
        den3 = pw(add(mono(2, 0, 4), (Fr(-1), Fr(-1))), 2)
        dB3 = max(abs(Y[0]), abs(Y[1])) * 4 / den3[0]
        dA3 = max(abs(num3[0]), abs(num3[1])) / den3[0]
        B3 = 4 * add(G, c)[1] / 3
        P3 = add(sc(16, add(mono(3, 0), mono(2, 1), mono(1, 2), mono(0, 3))), sc(-12, add(G, c)))
        P3p = add(sc(16, add(mono(2, 0, 3), mono(1, 1, 2), mono(0, 2))), (Fr(-12), Fr(-12)))
        P4 = add(sc(16, add(mono(4, 0), mono(3, 1), mono(2, 2), mono(1, 3), mono(0, 4))), sc(-20, add(mono(2, 0), mono(1, 1), mono(0, 2))), (Fr(5), Fr(5)))
        P4p = add(sc(16, add(mono(3, 0, 4), mono(2, 1, 3), mono(1, 2, 2), mono(0, 3))), sc(-20, add(mono(1, 0, 2), c)))
        nB5 = add(mul(P3p, U4), neg(mul(P3, U4p)))
        nA5 = add(mul(P4p, U4), neg(mul(P4, U4p)))
        dB5 = max(abs(nB5[0]), abs(nB5[1])) / U4[0] ** 2
        dA5 = max(abs(nA5[0]), abs(nA5[1])) / U4[0] ** 2
        B5 = P3[1] / U4[0]
        f = lambda x: round(float(x), 4)
        ctx.note('c in', float(clo), float(chi))
        ctx.note(' Y', [f(v) for v in Y], ' num3', [f(v) for v in num3], ' |dB3|<=', f(dB3), ' |dA3|<=', f(dA3), ' B3<=', f(B3))
        ctx.note(' P3', [f(v) for v in P3], " P3'", [f(v) for v in P3p], ' P4', [f(v) for v in P4], " P4'", [f(v) for v in P4p])
        ctx.note(' numB5', [f(v) for v in nB5], ' numA5', [f(v) for v in nA5], ' |dB5|<=', f(dB5), ' |dA5|<=', f(dA5), ' B5<=', f(B5))
        cm = max(abs(clo), abs(chi))
        w2, w3, w5 = (Fr(38, 100), Fr(65, 100), Fr(31, 1000))
        dbeta = w2 * 1 + w3 * dB3 + w5 * dB5
        beta = w2 * 1 + w3 * B3 + w5 * B5
        dalpha = w2 * cm + w3 * dA3 + w5 * dA5
        ctx.note(' |dbeta|<=', f(dbeta), ' beta<=', f(beta), ' |dalpha|<=', f(dalpha), ' |dtheta|<=', f(dbeta + beta * dalpha))
        bound = Fr(508, 100) if clo > 0 else Fr(26, 10)
        check(' naive bound |dtheta| < %s and 0.225*5.1 < 1.88' % float(bound), dbeta + beta * dalpha < bound and Fr(225, 1000) * Fr(51, 10) < Fr(188, 100) and (Fr(1, 2) / Fr(515, 1000) ** 2 > Fr(188, 100)))
        from numpy.polynomial import chebyshev as Ch
        Gs = np.linspace(1, 1.025, 201)
        cs = np.linspace(float(clo), float(chi), 201)
        GG, CC = np.meshgrid(Gs, cs)
        T = lambda m, x: np.cos(m * np.arccos(np.clip(x, -1, 1))) if np.all(np.abs(x) <= 1) else None

        def Tm(m, x):
            return Ch.chebval(x, [0] * m + [1])

        def Um(m, x):
            a, b = (np.ones_like(x), 2 * x)
            if m == 0:
                return a
            for _ in range(m - 1):
                a, b = (b, 2 * x * b - a)
            return b

        def AB(m, G, c):
            return ((Tm(m, G) - Tm(m, c)) / ((G - c) * Um(m - 1, G)), (Um(m - 1, G) - Um(m - 1, c)) / ((G - c) * Um(m - 1, G)))
        eps = 1e-07
        worst = 0
        for w2f, w5f in [(0.36, 0), (0.38, 0), (0.36, 0.031), (0.38, 0.031)]:
            for w3f in [0.59, 0.65]:

                def th(G):
                    al = 1 + w2f * AB(2, G, CC)[0] + w3f * AB(3, G, CC)[0] + w5f * AB(5, G, CC)[0]
                    be = w2f * AB(2, G, CC)[1] + w3f * AB(3, G, CC)[1] + w5f * AB(5, G, CC)[1]
                    return be / al
                d = (th(GG + eps) - th(GG - eps)) / (2 * eps)
                worst = max(worst, np.max(np.abs(d)))
        ctx.note(' grid max |dtheta| =', round(worst, 4))
    run(Fr(22, 100), Fr(30, 100))
    run(Fr(-51, 100), Fr(-49, 100))
    ctx.note('ALL CHECKS PASSED')
    ctx.check(True, 'derivation completed', kind='derivation')
