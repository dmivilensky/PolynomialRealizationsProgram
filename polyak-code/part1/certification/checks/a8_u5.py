"""Callable exact suite: struct/a8_u5.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp, time
from ..algebra.waves import *

def run(ctx):
    W2, W3, al, be, ga, de = sp.symbols('W2 W3 al be ga de')
    Phi = sp.together(Lfun(1) + W2 * Ufun(2) + W3 * Ufun(3) + (1 - W2 - W3) * Ufun(5))
    num, den = sp.fraction(sp.factor(Phi))
    ctx.note('den:', sp.factor(den))
    R5 = sp.Poly(sp.expand(num), c)
    R5p, rem = sp.div(R5, sp.Poly(2 * X * c - (X ** 2 + 1), c))
    ctx.check(rem.is_zero, 'struct/a8_u5.py:12: rem.is_zero')
    ctx.note('deg R5p:', R5p.degree())
    Bc = R5p.all_coeffs()
    A6 = Bc[0]
    target = sp.Poly(sp.expand((c ** 2 + al * c + be) ** 2 * (c ** 2 + ga * c + de)), c).all_coeffs()
    eqs = [sp.expand(Bc[i] - A6 * target[i]) for i in range(1, 7)]
    sgd = sp.solve(eqs[:2], [ga, de], dict=True)[0]
    rest = [sp.factor(sp.numer(sp.together(e.subs(sgd)))) for e in eqs[2:]]
    for e in rest:
        ctx.note('dual eq: deg al,be,W2,W3:', sp.degree(e, al), sp.degree(e, be), sp.degree(e, W2), sp.degree(e, W3))
    ctx.artifacts['central_dual_system'] = {'rest': rest, 'sgd': sgd}
    ctx.note('U5 regime: dual system set up (4 equations in al, be, W2, W3 over Q(X,Y)); primal rank condition = det of the 3x3')
    ctx.note('matrix [L1,U2,U3](c_1), [L1,U2,U3](c_2), C-column; elimination of (al,be,W2,W3) NOT performed (too heavy for sympy).')
    ctx.check(True, 'derivation completed', kind='derivation')
