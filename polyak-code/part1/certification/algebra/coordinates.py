"""Exact reusable algebra, refactored from the supplied Part I computations.
See PROVENANCE.json for original source hashes.
"""
"""express a polynomial D(X,Y), palindromic in X and 'anti-palindromic-compatible' in Y, via ch t and sh v."""
import sympy as sp
from .waves import X, Y
cs, ss = sp.symbols('ch_t sh_v')

def to_cs(D, dx, dy):
    """D(X,Y)/(X^dx Y^dy) as polynomial in ch t = (X+1/X)/2, sh v = (Y-1/Y)/2 (if possible)."""
    e = sp.expand(D / (X ** dx * Y ** dy))
    coeffs = sp.symbols('k0:%d' % ((dx + 1) * (dy + 1)))
    P = 0
    i = 0
    for a in range(dx + 1):
        for b in range(dy + 1):
            P += coeffs[i] * cs ** a * ss ** b
            i += 1
    Pe = sp.expand(P.subs({cs: (X + 1 / X) / 2, ss: (Y - 1 / Y) / 2}))
    eqs = sp.Poly(sp.expand((Pe - e) * X ** dx * Y ** dy), X, Y).coeffs()
    sol = sp.solve(eqs, coeffs, dict=True)
    if not sol:
        return None
    return sp.factor(P.subs(sol[0]).subs({k: 0 for k in coeffs}))
