"""Callable exact suite: struct/a9_kc_slopes.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp

def run(ctx):
    c, E, s = sp.symbols('c E s')
    h = (1 - c ** 2 - s ** 2) * (E - c) - 2 * s * (1 - c ** 2)
    pt = {c: -sp.Rational(1, 2), E: 1, s: sp.Rational(1, 2)}
    ctx.note('h, h_c, h_cc at point:', [sp.simplify(e.subs(pt)) for e in (h, sp.diff(h, c), sp.diff(h, c, 2))])
    sp1 = sp.simplify(-sp.diff(h, E).subs(pt) / sp.diff(h, s).subs(pt))
    ctx.note("s_1'(1) =", sp1)
    beta = sp.simplify(sp1 / sp.sqrt(1 + sp.Rational(1, 4)))
    ctx.note('beta = d/dtau asinh(s_1(e^tau)) at 0 =', sp.radsimp(beta), '=', sp.N(beta))
    ctx.note('right slope factor 1/(1-beta) =', sp.radsimp(1 / (1 - beta)), '=', sp.N(1 / (1 - beta)))
    ctx.note('left  slope factor 1/(1+beta) =', sp.radsimp(1 / (1 + beta)), '=', sp.N(1 / (1 + beta)))
    ctx.note('h(1) = -s^2 (E-1):', sp.factor(h.subs(c, 1)))
    ctx.check(True, 'derivation completed', kind='derivation')
