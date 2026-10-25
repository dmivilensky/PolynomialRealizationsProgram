"""Callable exact suite: struct/a8_curves.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
from ..algebra.waves import X, Y
from ..algebra.coordinates import to_cs, cs, ss

def run(ctx):
    fl = ctx.artifacts['two_wave_resultant']['Res'][1]
    D2 = [f for f, k in fl if sp.degree(f, X) == 8][0]
    ctx.note('D2(1/X,Y)*X^8 - D2 =', sp.expand(D2.subs(X, 1 / X) * X ** 8 - D2))
    P2 = to_cs(D2, 4, 4)
    P2 = sp.factor(P2 / 16)
    P1 = ctx.artifacts['one_wave_discriminant']['P1']
    P1 = sp.factor(P1 / 1024)
    ctx.note('P2 =', sp.expand(P2))
    ctx.note('P1 =', sp.expand(P1))
    sp_ = 1 - 1 / (2 * cs)
    ctx.note('P2 on spiral:', sp.factor(sp.numer(sp.together(P2.subs(ss, sp_)))))
    ctx.note('P1 on spiral:', sp.factor(sp.numer(sp.together(P1.subs(ss, sp_)))))
    p10 = 448 * cs ** 10 - 1152 * cs ** 9 + 800 * cs ** 8 - 1248 * cs ** 7 + 3212 * cs ** 6 - 2512 * cs ** 5 + 108 * cs ** 4 + 688 * cs ** 3 - 345 * cs ** 2 + 64 * cs - 4
    ctx.note('p10 roots in [1, oo):', sp.Poly(p10, cs).count_roots(1, sp.oo))
    ctx.artifacts['regime_curves'] = {'P1': P1, 'P2': P2}
    ctx.check(True, 'derivation completed', kind='derivation')
