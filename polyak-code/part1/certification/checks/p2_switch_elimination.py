"""Callable exact suite: extensions/p2_u5.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as s, time, json

def run(ctx):
    G, u, c, W = s.symbols('G u c W')
    P2 = 256 * G ** 4 * u ** 2 - 256 * G ** 4 - 512 * G ** 3 * u ** 3 + 768 * G ** 3 * u - 32 * G ** 2 * u ** 4 - 480 * G ** 2 * u ** 2 - 16 * G * u ** 3 - u ** 4 - 16 * u ** 2
    p = s.Poly(P2, u, domain='QQ(G)')

    def red(e):
        n, d = s.fraction(s.cancel(e))
        return s.rem(s.Poly(n, u, domain='QQ(G)') * s.invert(s.Poly(d, u, domain='QQ(G)'), p), p).as_expr()

    def mul(a, b):
        return red(a * b)

    def div(a, b):
        return red(a / b)
    k = 1 - c * c
    M = 8 * G ** 3 + 4 * G ** 2 * c - G + (1 - W) * (4 * G * c * c - 3 * G) - W * (G + c)
    N = W * (4 * G * G - 1) + 4 * (1 - W) * G * (G + c)
    co = s.Poly(-((k - u * u) * M - 2 * u * k * N), c).all_coeffs()
    A, B, C, D, E = co
    e1 = s.cancel((8 * A * A * D - B * (4 * A * C - B * B)) / (4 * G * G - W))
    e2 = s.expand(64 * A ** 3 * E - (4 * A * C - B * B) ** 2)
    lin = s.Poly(s.subresultants(e2, e1, W)[-2], W)
    ww = div(-lin.coeff_monomial(1), lin.coeff_monomial(W))
    ctx.note('W computed', flush=True)
    aa = div(red(B.subs(W, ww)), 2 * red(A.subs(W, ww)))
    bb = div(red(C.subs(W, ww)) - mul(red(A.subs(W, ww)), mul(aa, aa)), 2 * red(A.subs(W, ww)))
    ctx.note('atom polynomial computed', flush=True)
    mom = [s.Integer(1), u]

    def coeffs(expr):
        pol = s.Poly(expr, c)
        v = [s.Integer(0), s.Integer(0)]
        for coeff in pol.all_coeffs():
            v = [red(coeff - mul(bb, v[1])), red(v[0] - mul(aa, v[1]))]
        return v

    def lf(m):
        return ((1 - c * c - u * u) * (s.chebyshevt(m, G) - s.chebyshevt(m, c)) - 2 * u * (1 - c * c) * s.chebyshevu(m - 1, c)) / s.chebyshevu(m - 1, G)

    def uf(m):
        return ((1 - c * c - u * u) * (s.chebyshevt(m, G) - s.chebyshevt(m, c)) + 2 * u * (1 - c * c) * s.chebyshevu(m - 1, c)) / s.chebyshevu(m - 1, G)
    l = coeffs(lf(1))
    v2 = coeffs(uf(2))
    mc = div(-l[0] - v2[0], l[1] + v2[1])
    d = red(-l[0] - mul(l[1], mc))
    ctx.note('moment and C*sinh(t) computed', flush=True)
    v5 = coeffs(uf(5))
    sl5 = red(v5[0] + mul(v5[1], mc) - d)
    ctx.note('U5 expression computed', flush=True)
    num, den = s.fraction(s.cancel(sl5))
    ctx.note('U5 numerator degree', s.Poly(num, G, u).degree_list(), flush=True)
    rr = s.factor(s.resultant(P2, num, u))
    ctx.note('U5 resultant', rr, flush=True)
    for fac, mult in s.factor_list(rr)[1]:
        pp = s.Poly(fac, G)
        n = pp.count_roots(s.Rational(102, 100), s.Rational(104, 100))
        if n:
            ctx.note('factor', fac, 'multiplicity', mult, 'roots', pp.intervals(eps=s.Rational(1, 10 ** 12), inf=s.Rational(102, 100), sup=s.Rational(104, 100)), flush=True)
    Ha = 162529280000 * G ** 12 - 238685519872 * G ** 10 + 77668708352 * G ** 8 - 6246545408 * G ** 6 - 58821872 * G ** 4 + 12933112 * G ** 2 + 229441
    lo, hi = (s.Rational(51, 50), s.Rational(26, 25))
    ctx.check(s.rem(s.Poly(rr, G), s.Poly(Ha, G)).is_zero, 'extensions/p2_u5.py:44: s.rem(s.Poly(rr, G), s.Poly(Ha, G)).is_zero')
    ctx.check(s.Poly(Ha, G).count_roots(lo, hi) == 1, 'extensions/p2_u5.py:45: s.Poly(Ha, G).count_roots(lo, hi) == 1')
    ctx.check(s.Poly(Ha, G).count_roots(s.Rational(864696, 844775), s.Rational(2018087, 1971594)) == 1, 'extensions/p2_u5.py:46: s.Poly(Ha, G).count_roots(s.Rational(864696, 844775), s.Rational(2018087, 1971594)) == 1')
    for fac, mult in s.factor_list(rr)[1]:
        if s.rem(s.Poly(fac, G), s.Poly(Ha, G)).is_zero:
            continue
        ctx.check(s.Poly(fac, G).count_roots(lo, hi) == 0, 'extensions/p2_u5.py:49: s.Poly(fac, G).count_roots(lo, hi) == 0')
    ctx.check(red(e1.subs(W, ww)) == 0, 'extensions/p2_u5.py:50: red(e1.subs(W, ww)) == 0')
    ctx.check(red(e2.subs(W, ww)) == 0, 'extensions/p2_u5.py:51: red(e2.subs(W, ww)) == 0')
    for name, expr in [('W', ww), ('a', aa), ('b', bb), ('mean', mc), ('d', d), ('U5', sl5)]:
        den = s.fraction(s.cancel(expr))[1]
        ctx.check(not den.has(u), 'extensions/p2_u5.py:54: not den.has(u)')
        ctx.check(s.Poly(den, G).count_roots(lo, hi) == 0, 'extensions/p2_u5.py:55: s.Poly(den, G).count_roots(lo, hi) == 0')
    ctx.note('Resultant and denominator checks: OK; physical branch selection is not asserted.')
    ctx.check(True, 'derivation completed', kind='derivation')
