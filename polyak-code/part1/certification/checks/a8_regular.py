"""Callable exact suite: struct/a8_regular.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
from ..algebra.coordinates import cs, ss

def run(ctx):
    d = ctx.artifacts['regime_curves']
    P1, P2 = (d['P1'], d['P2'])
    Psp = 2 * cs * ss - 2 * cs + 1

    def check(P, name, lo, hi):
        P = sp.factor_list(P)[1]
        P = [f for f, k in P if f.has(ss)][0]
        Ps, Pc = (sp.diff(P, ss), sp.diff(P, cs))
        r1 = sp.Poly(sp.resultant(P, Ps, ss), cs)
        Nn = sp.expand(Ps ** 2 * (1 + ss ** 2) - Pc ** 2 * (cs ** 2 - 1))
        r2 = sp.Poly(sp.resultant(P, Nn, ss), cs)
        n1 = r1.count_roots(lo, hi) if r1.degree() > 0 else 0
        n2 = r2.count_roots(lo, hi) if r2.degree() > 0 else 0
        ctx.note('%s: #real roots in [%s, %s] of Res(P,P_s): %d ; of Res(P,N): %d' % (name, lo, hi, n1, n2))
        ctx.check(n1 == n2 == 0, 'struct/a8_regular.py:20: n1 == n2 == 0')
        return (r1, r2)
    check(Psp, 'spiral', 1, sp.oo)
    c1 = sp.real_roots(sp.Poly(32 * cs ** 3 - 36 * cs ** 2 + 4 * cs - 1, cs))[0]
    lo2 = sp.Rational(10201, 10000)
    ctx.note('ch(0.2) =', sp.N(sp.cosh(sp.Rational(1, 5))), ' ch t_a (t_a~0.2149) ~', sp.N(sp.cosh(sp.Rational(2149, 10000))), ' c_1 =', sp.N(c1))
    check(P2, 'two-atom P2', sp.Rational(102, 100), sp.Rational(104, 100))
    check(P1, 'one-wave P1', sp.Rational(136, 100), sp.oo)
    ctx.check(True, 'derivation completed', kind='derivation')
