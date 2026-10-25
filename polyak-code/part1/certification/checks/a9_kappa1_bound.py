"""Callable exact suite: struct/a9_kappa1_bound.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp

def run(ctx):
    c, y, x = sp.symbols('c y x')
    s = 1 - y + y ** 2
    h = (1 - c ** 2 - s ** 2) * (1 / y - c) - 2 * s * (1 - c ** 2)
    P = sp.expand(-h * y)
    ctx.note('-h*y =', sp.collect(P, c))
    A = 1 - 2 * y + 2 * y ** 2 - 2 * y ** 3
    B = 2 * y ** 2 - 3 * y ** 3 + 2 * y ** 4 - y ** 5
    D = y ** 2 + y ** 4
    ctx.note('identity check:', sp.expand((A - c * y) * c ** 2 + B * c + D - P))
    amin = A - y
    G = sp.expand((4 * amin * D - B ** 2) / y ** 2)
    ctx.note('G/y^2 =', G)
    for name, poly_ in (('A - y', amin), ('G', G)):
        pp = sp.Poly(poly_, y)
        ctx.note(name, ': value at 1/4 =', pp.eval(sp.Rational(1, 4)), '; #roots in [0,1/4] =', pp.count_roots(0, sp.Rational(1, 4)), '; value at 0 =', pp.eval(0))
    ctx.note('=> for 0<y<=1/4: A-cy >= A-y > 0 and -h*y >= D - B^2/(4(A-y)) > 0 on [-1,1].')
    ctx.check(sp.expand((A - c * y) * c ** 2 + B * c + D - P) == 0, 'struct/a9_kappa1_bound.py:22: sp.expand((A - c * y) * c ** 2 + B * c + D - P) == 0')
    for pp in [sp.Poly(amin, y), sp.Poly(G, y)]:
        ctx.check(pp.count_roots(0, sp.Rational(1, 4)) == 0, 'struct/a9_kappa1_bound.py:24: pp.count_roots(0, sp.Rational(1, 4)) == 0')
        ctx.check(pp.eval(0) > 0 and pp.eval(sp.Rational(1, 4)) > 0, 'struct/a9_kappa1_bound.py:25: pp.eval(0) > 0 and pp.eval(sp.Rational(1, 4)) > 0')
    ctx.check(True, 'derivation completed', kind='derivation')
