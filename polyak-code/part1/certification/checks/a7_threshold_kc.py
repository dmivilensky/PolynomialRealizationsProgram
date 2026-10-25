"""Callable exact suite: struct/a7_threshold_kc.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp

def run(ctx):
    c, s, E, x, y = sp.symbols('c s E x y')
    r5 = sp.sqrt(5)
    phi = (1 + r5) / 2
    h = (1 - c ** 2 - s ** 2) * (E - c) - 2 * s * (1 - c ** 2)
    ctx.note('dh/ds =', sp.factor(sp.diff(h, s)), '  (= -2 s (E - c) - 2(1-c^2) <= 0 for s>=0, c in [-1,1], E>=1)')
    sE = (phi * E - 1 / (phi * E)) / 2
    P = sp.expand(-h.subs(s, sE) * 4 * phi ** 2 * E ** 2)
    P = sp.expand(sp.simplify(P))
    Pxy = sp.expand(P.subs({c: 1 - 2 * x, E: 1 + y}))
    Pxy = sp.expand(sp.radsimp(Pxy))
    poly = sp.Poly(Pxy, x, y)
    ctx.note('monomials of -h*4phi^2E^2 in x=(1-c)/2, y=E-1:')
    neg = []
    for mon, co in zip(poly.monoms(), poly.coeffs()):
        co = sp.nsimplify(sp.radsimp(co))
        ctx.note('  x^%d y^%d :' % mon, co, '  ~', sp.N(co, 8))
        if sp.N(co) < 0:
            neg.append((mon, co))
    ctx.note('negative coefficients:', neg)
    Px = sp.Poly(Pxy, x)
    A3, A2, A1, A0 = [sp.expand(sp.radsimp(co)) for co in Px.all_coeffs()]
    ctx.note('A3 =', sp.factor(A3))
    ctx.note('A0 =', sp.factor(A0))
    G = sp.expand(sp.radsimp(4 * A1 * A3 - A2 ** 2))
    Gp = sp.Poly(G, y)
    ctx.note('4 A1 A3 - A2^2 coefficients in y (must be >= 0):')
    for k, co in zip(range(Gp.degree(), -1, -1), Gp.all_coeffs()):
        ctx.note(k, co)

    def nonneg(co):
        co = sp.expand(co)
        b_ = co.coeff(r5)
        a_ = sp.expand(co - b_ * r5)
        ctx.check(a_.is_rational and b_.is_rational, 'struct/a7_threshold_kc.py:38: a_.is_rational and b_.is_rational')
        if a_ >= 0 and b_ >= 0:
            return True
        if a_ >= 0 and b_ < 0:
            return a_ ** 2 >= 5 * b_ ** 2
        if a_ < 0 and b_ >= 0:
            return 5 * b_ ** 2 >= a_ ** 2
        return False
    ctx.check(all((nonneg(sp.radsimp(co)) for co in Gp.all_coeffs())), 'struct/a7_threshold_kc.py:43: all((nonneg(sp.radsimp(co)) for co in Gp.all_coeffs()))')
    ctx.check(all((nonneg(sp.radsimp(co)) for co in sp.Poly(A0, y).all_coeffs())), 'struct/a7_threshold_kc.py:44: all((nonneg(sp.radsimp(co)) for co in sp.Poly(A0, y).all_coeffs()))')
    ctx.check(all((nonneg(sp.radsimp(co)) for co in sp.Poly(A3, y).all_coeffs())), 'struct/a7_threshold_kc.py:45: all((nonneg(sp.radsimp(co)) for co in sp.Poly(A3, y).all_coeffs()))')
    ctx.note('EXACT: A3 > 0, A0 >= 0 (A0 > 0 for y > 0), 4A1A3 - A2^2 >= 0 for y >= 0  =>  -h >= 0, and -h > 0 for E > 1.')
    D = sp.factor(sp.discriminant(sp.expand(h), c))
    ctx.note('disc_c h =', D)
    ctx.check(True, 'derivation completed', kind='derivation')
