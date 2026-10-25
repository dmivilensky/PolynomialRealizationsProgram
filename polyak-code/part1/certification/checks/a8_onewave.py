"""Callable exact suite: struct/a8_onewave.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
from ..algebra.waves import *
from ..algebra.coordinates import to_cs, cs, ss

def run(ctx):
    d = ctx.artifacts['threshold_system']
    R1 = sp.Poly(sp.expand(d['R1']), c)
    R10 = sp.Poly(R1.as_expr().subs(W, 0), c)
    ctx.note('R1|W=0 coefficients:', [sp.factor(x) for x in R10.all_coeffs()])
    D1 = sp.factor(sp.discriminant(R10.as_expr(), c))
    fl = sp.factor_list(D1)
    for f, k in fl[1]:
        ctx.note(sp.degree(f, X), sp.degree(f, Y), k, str(f)[:120])
    main = [f for f, k in fl[1] if sp.degree(f, X) > 2][0]
    dx = sp.degree(main, X) // 2
    dy = sp.degree(main, Y) // 2
    P1 = to_cs(main, dx, dy)
    ctx.note('one-wave curve P1(ch t, sh v) =', P1)
    ctx.artifacts['one_wave_discriminant'] = {'D1': main, 'P1': P1, 'R10': R10.as_expr()}
    ctx.check(True, 'derivation completed', kind='derivation')
