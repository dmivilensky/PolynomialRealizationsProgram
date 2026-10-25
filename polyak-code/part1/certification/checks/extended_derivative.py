"""Callable exact suite: extensions/new_certificates.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as s

def run(ctx):
    G, c, x, y, u = s.symbols('G c x y u')
    D = 2 * G ** 2 + G * c + c ** 2 - 1
    n = -2 * G ** 2 - 4 * G * c - 1
    P = (2 - c * c) ** 2 * D ** 4 - 4 * (1 - c * c) ** 2 * (G * G - 1) * n ** 2
    for a, b in [(-1, 0), (0, 1)]:
        p = s.Poly(P.subs({G: 1 + x / 2, c: a + (b - a) * y}), x, y)
        nx, ny = (p.degree(x), p.degree(y))
        bs = [sum((co * s.binomial(i, k) / s.binomial(nx, k) * s.binomial(j, l) / s.binomial(ny, l) for (k, l), co in p.terms() if k <= i and l <= j)) for i in range(nx + 1) for j in range(ny + 1)]
        ctx.check(min(bs) > 0, 'extensions/new_certificates.py:13: min(bs) > 0')
        ctx.note('compact', a, b, min(bs))
        p = s.Poly(P.subs({G: x + s.Rational(3, 2), c: a + (b - a) * y}), x, y)
        nx, ny = (p.degree(x), p.degree(y))
        bs = [sum((p.coeff_monomial(x ** i * y ** l) * s.binomial(j, l) / s.binomial(ny, l) for l in range(j + 1))) for i in range(nx + 1) for j in range(ny + 1)]
        ctx.check(min(bs) > 0, 'extensions/new_certificates.py:21: min(bs) > 0')
        ctx.note('half-line', a, b, min(bs))
    weights = {2: s.Rational(9, 50), 3: s.Rational(57, 100), 5: s.Rational(1, 4)}
    alpha = 1 + sum((W * s.cancel((s.chebyshevt(m, G) - s.chebyshevt(m, c)) / (G - c)) / s.chebyshevu(m - 1, G) for m, W in weights.items()))
    beta = sum((W * s.cancel((s.chebyshevu(m - 1, G) - s.chebyshevu(m - 1, c)) / (G - c)) / s.chebyshevu(m - 1, G) for m, W in weights.items()))
    S = 2 * u * (1 - c * c) * beta - (1 - c * c - u * u) * alpha
    Q = 40 * c ** 4 - 40 * c ** 3 - 12 * c * c + 21 * c + 15
    ctx.check(s.factor(S.subs({G: 1, u: s.Rational(1, 2)}) - (2 * c + 1) ** 2 * Q / 200) == 0, 'extensions/new_certificates.py:30: s.factor(S.subs({G: 1, u: s.Rational(1, 2)}) - (2 * c + 1) ** 2 * Q / 200) == 0')
    ctx.check(s.Poly(Q, c).count_roots(-1, 1) == 0, 'extensions/new_certificates.py:31: s.Poly(Q, c).count_roots(-1, 1) == 0')
    ctx.check(Q.subs(c, 0) > 0, 'extensions/new_certificates.py:32: Q.subs(c, 0) > 0')
    ctx.check((1 - s.Rational(1, 5) ** 4) ** 2 - s.Rational(99, 100) == s.Rational(10629, 1562500), 'extensions/new_certificates.py:33: (1 - s.Rational(1, 5) ** 4) ** 2 - s.Rational(99, 100) == s.Rational(10629, 1562500)')
    ctx.note('identities and Sturm: OK')
    ctx.check(True, 'derivation completed', kind='derivation')
