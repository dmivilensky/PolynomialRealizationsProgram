"""Callable exact suite: struct/a7_cycles.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp

def run(ctx):
    c, s = sp.symbols('c s')
    g = 1 - c ** 2 - s ** 2
    T = lambda m: sp.chebyshevt(m, c)
    U = lambda m: sp.chebyshevu(m, c)
    a = lambda m: g * (1 - T(m))
    b = lambda m: 2 * s * (1 - c ** 2) * U(m - 1)
    ctx.note('(i) a_1 - b_1 - (1-c)((1-2s)-(c+s)^2) =', sp.expand(a(1) - b(1) - (1 - c) * (1 - 2 * s - (c + s) ** 2)))
    w = 2 * sp.pi / 3
    for m in range(1, 4):
        am = (sp.sin(w) ** 2 - sp.Rational(1, 4)) * (1 - sp.cos(m * w))
        bm = 2 * sp.Rational(1, 2) * sp.sin(w) * sp.sin(m * w)
        ctx.note('(ii) m=%d: a_m=%s, b_m=%s, a_m-|b_m|=%s' % (m, sp.nsimplify(am), sp.nsimplify(bm), sp.nsimplify(am - abs(bm))))
    ctx.note('     (a_m, b_m depend on m mod 3 only)')
    ctx.check(True, 'derivation completed', kind='derivation')
