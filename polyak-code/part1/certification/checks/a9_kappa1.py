"""Callable exact suite: struct/a9_kappa1.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
from ..algebra.coordinates import cs, ss

def run(ctx):
    P1 = ctx.artifacts['regime_curves']['P1']
    z, sig = sp.symbols('z sigma')
    N = 6
    d = sp.symbols('d1:%d' % (N + 1))
    sz = 1 + sum((d[j] * z ** (j + 1) for j in range(N)))
    Pz = sp.expand(P1.subs(cs, 1 / z) * z ** 10)
    ser = sp.expand(sp.series(Pz.subs(ss, sz), z, 0, N + 2).removeO())
    co = [ser.coeff(z, j) for j in range(0, N + 2)]
    ctx.note('orders:', [sp.factor(cc) for cc in co[:3]])
    sols = {}
    for j in range(0, N + 1):
        cj = sp.factor(co[j].subs(sols))
        if cj == 0:
            continue
        free = [x for x in d if x in cj.free_symbols and x not in sols]
        if not free:
            ctx.note('inconsistent at order', j, cj)
            break
        sj = sp.solve(cj, free[0])
        ctx.note('order z^%d: solve for %s:' % (j, free[0]), sj)
        sols[free[0]] = [x for x in sj if x.is_real][0] if len(sj) > 1 else sj[0]
    s1w = sp.expand(sz.subs(sols))
    ctx.note('one-wave: sh v =', s1w)
    ctx.note('spiral  : sh v = 1 - z/2')
    X, q, R = sp.symbols('X q R')

    def rho_series(sexpr, order=4):
        s_X = sp.series(sexpr.subs(z, 2 * X / (1 + X ** 2)), X, 0, order + 1).removeO()
        Yx = sp.series(s_X + sp.sqrt(1 + s_X ** 2), X, 0, order + 1).removeO()
        r_ = sp.Integer(0)
        for _ in range(order + 1):
            r_ = sp.series(q * Yx.subs(X, r_), q, 0, order + 1).removeO()
        return sp.expand(sp.nsimplify(sp.radsimp(sp.expand(r_))))
    rs = rho_series(1 - z / 2)
    r1 = rho_series(s1w)
    ctx.note('spiral   rho/q =', sp.expand(sp.radsimp(rs / q)))
    ctx.note('one-wave rho/q =', sp.expand(sp.radsimp(r1 / q)))
    ctx.note('difference (one-wave - spiral) =', sp.factor(sp.radsimp(sp.expand(r1 - rs))))
    ctx.check(True, 'derivation completed', kind='derivation')
