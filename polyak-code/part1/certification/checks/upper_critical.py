"""Callable exact suite: upper/kc_cert.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
from ..algebra.bernstein import certify_positive

def run(ctx):
    c, G, u = sp.symbols('c G u')
    T = sp.chebyshevt
    U = sp.chebyshevu
    qc = (sp.sqrt(5) - 1) / 2
    ctx.note('(a) sh(-ln q_c) = (1/q_c - q_c)/2 =', sp.nsimplify(sp.simplify((1 / qc - qc) / 2)))
    lam = sp.Rational(-1, 2) + sp.sqrt(3) * sp.I / 2
    s = sp.expand(sp.radsimp((lam + qc ** 2 / lam) / (2 * qc)))
    res, ims = (sp.re(s), sp.im(s))
    g = sp.radsimp(sp.expand(1 - res ** 2 - ims ** 2))
    ctx.note('    s = S(lambda) =', s, '; g = 1-|s|^2 =', g, '; Im s =', ims)
    ctx.check(sp.simplify(g - sp.Rational(1, 2)) == 0 and sp.simplify(ims - sp.sqrt(3) / 4) == 0, 'upper/kc_cert.py:19: sp.simplify(g - sp.Rational(1, 2)) == 0 and sp.simplify(ims - sp.sqrt(3) / 4) == 0')
    cw = {1: -sp.Rational(1, 2), 2: -sp.Rational(1, 2), 3: 1}
    sw = {1: sp.sqrt(3) / 2, 2: -sp.sqrt(3) / 2, 3: 0}
    for m in (1, 2, 3):
        a = sp.Rational(1, 2) * (1 - cw[m])
        b = 2 * (sp.sqrt(3) / 4) * sw[m]
        ctx.note('    m=%d: a_m=%s, b_m=%s, |b_m| <= a_m: %s (equality: %s)' % (m, a, b, sp.Abs(b) <= a, sp.Abs(b) == a))
    ctx.note('    (at t=0 the constraints are 3-periodic in m; star: |C|=0 < g)')
    Wd = {2: sp.Rational(9, 50), 3: sp.Rational(57, 100), 5: sp.Rational(1, 4)}
    ctx.check(sum(Wd.values()) == 1, 'upper/kc_cert.py:26: sum(Wd.values()) == 1')
    al = 1 + sum((Wd[m] * sp.cancel((T(m, G) - T(m, c)) / (G - c)) / U(m - 1, G) for m in Wd))
    be = sum((Wd[m] * sp.cancel((U(m - 1, G) - U(m - 1, c)) / (G - c)) / U(m - 1, G) for m in Wd))
    k = 1 - c ** 2
    S0 = sp.expand((2 * u * k * be - (k - u ** 2) * al).subs({G: 1, u: sp.Rational(1, 2)}))
    R = 40 * c ** 4 - 40 * c ** 3 - 12 * c ** 2 + 21 * c + 15
    ctx.note('(b) S(c) - (c+1/2)^2 R(c)/50 =', sp.expand(S0 - (c + sp.Rational(1, 2)) ** 2 * R / 50))
    ctx.note('    roots of R in [-1,1] (Sturm):', sp.Poly(R, c).count_roots(-1, 1), ', R(0) =', R.subs(c, 0))
    den = U(1, G) * U(2, G) * U(4, G)
    A = sp.factor(sp.cancel(al * den))
    B = sp.factor(sp.cancel(be * den))
    ctx.check(sp.cancel(A / den - al) == 0 and sp.cancel(B / den - be) == 0, 'upper/kc_cert.py:36: sp.cancel(A / den - al) == 0 and sp.cancel(B / den - be) == 0')
    A = sp.expand(A)
    B = sp.expand(B)
    num = sp.expand(sp.diff(B, G) * A - B * sp.diff(A, G))
    box = [(1, sp.Rational(11, 10)), (-1, 1)]
    okA = certify_positive(A, (G, c), box)
    okD = certify_positive(den, (G,), box[:1])
    Pi = sp.expand((2 - c ** 2) ** 2 * A ** 4 - 4 * (1 - c ** 2) ** 2 * (G ** 2 - 1) * num ** 2)
    okP = certify_positive(Pi, (G, c), box)
    ctx.note('(c) A > 0:', okA, '; denominator > 0:', okD, '; Pi_5 > 0 on [1,11/10]x[-1,1]:', okP)
    chmax = sp.simplify((qc * (1 + sp.sqrt(2)) + 1 / (qc * (1 + sp.sqrt(2)))) / 2)
    ctx.note('    ch t_max =', chmax, '=', sp.N(chmax, 12), '< 11/10:', ctx.check(sp.simplify(chmax - sp.Rational(11, 10)) < 0, 'upper/kc_cert.py:45: sp.simplify(chmax - sp.Rational(11, 10)) < 0'))
    ctx.check(okA[0] and okD[0] and okP[0], 'upper/kc_cert.py:46: okA[0] and okD[0] and okP[0]')
    ctx.check(True, 'derivation completed', kind='derivation')
