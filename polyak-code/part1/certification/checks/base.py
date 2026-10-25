"""Callable exact suite: base/base_check.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp

def run(ctx):
    r, c, q, t, g, C, B, G = sp.symbols('rho c q t g C B G', real=True)
    ch = lambda x: (sp.exp(x) + sp.exp(-x)) / 2
    U = lambda m: sp.chebyshevu(m - 1, c)
    T = lambda m: sp.chebyshevt(m, c)
    chm = lambda m: (r ** m + r ** (-m)) / 2
    shm = lambda m: (r ** m - r ** (-m)) / 2
    eqs = [g * (chm(1) - T(1)) + C * shm(1) - B * U(1), g * (chm(2) - T(2)) - C * shm(2) + B * U(2), g * (chm(3) - T(3)) - C * shm(3) + B * U(3)]
    Mx = sp.Matrix([[sp.diff(e, v) for v in (g, C, B)] for e in eqs])
    det = sp.factor(sp.simplify(Mx.det()))
    ctx.note('det =', det)
    target = (r ** 2 - 1) * (r ** 2 - 2 * c * r + 1) ** 2 * (c * (r ** 2 + 1) + r) / r ** 4
    ctx.note('det identity:', ctx.check(sp.simplify(det - target) == 0, 'base/base_check.py:15: sp.simplify(det - target) == 0'))
    cw = -r / (1 + r ** 2)
    sol = sp.solve([e.subs(c, cw) for e in eqs[:2]], [C, B], dict=True)[0]
    ctx.note('C =', sp.factor(sol[C]), ' B =', sp.factor(sol[B]))
    ctx.note('C==g th t:', ctx.check(sp.simplify(sol[C] - g * (r ** 2 - 1) / (r ** 2 + 1)) == 0, 'base/base_check.py:19: sp.simplify(sol[C] - g * (r ** 2 - 1) / (r ** 2 + 1)) == 0'), ' B formula:', ctx.check(sp.simplify(sol[B] - g * (r ** 4 + r ** 2 + 1) / (r * (r ** 2 + 1))) == 0, 'base/base_check.py:19: sp.simplify(sol[B] - g * (r ** 4 + r ** 2 + 1) / (r * (r ** 2 + 1))) == 0'), ' U3 residual:', ctx.check(sp.simplify(eqs[2].subs(c, cw).subs(sol)) == 0, 'base/base_check.py:19: sp.simplify(eqs[2].subs(c, cw).subs(sol)) == 0'))
    cc = (r + 1 / r) / 2
    sin2 = 1 - cw ** 2
    shv = sp.symbols('shv')
    gsol = sp.solve(sp.Eq(2 * shv * sin2, g * (r ** 4 + r ** 2 + 1) / (r * (r ** 2 + 1))), g)[0]
    ctx.note('g = sh v / ch t :', ctx.check(sp.simplify(gsol - shv / cc) == 0, 'base/base_check.py:26: sp.simplify(gsol - shv / cc) == 0'))
    quad = sp.expand(sin2 - shv ** 2 - shv / cc)
    ctx.note('roots sh v:', [sp.simplify(x) for x in sp.solve(quad, shv)])
    F = r ** 2 * (r ** 2 + 1) - 2 * q * r * (r ** 2 - r + 1) - q ** 2 * (r ** 2 + 1)
    H = (r - q) ** 2 * (r ** 2 + 1) - 2 * q * (q - (1 - q) * r ** 2)
    ctx.note('H==F:', ctx.check(sp.expand(H - F) == 0, 'base/base_check.py:31: sp.expand(H - F) == 0'))
    shv_r = (r / q - q / r) / 2
    ctx.note('2q rho (1+rho^2)(sh v -1 + 1/(2ch t)) == F :', ctx.check(sp.simplify(2 * q * r * (1 + r ** 2) * (shv_r - 1 + 1 / (2 * cc)) - F) == 0, 'base/base_check.py:33: sp.simplify(2 * q * r * (1 + r ** 2) * (shv_r - 1 + 1 / (2 * cc)) - F) == 0'))
    qr = r * (sp.sqrt((r ** 2 - r + 1) ** 2 + (r ** 2 + 1) ** 2) - (r ** 2 - r + 1)) / (r ** 2 + 1)
    ctx.note('F(rho,q(rho))==0:', ctx.check(sp.simplify(sp.expand(F.subs(q, qr))) == 0, 'base/base_check.py:35: sp.simplify(sp.expand(F.subs(q, qr))) == 0'))
    ctx.note('q(1)=', sp.nsimplify(sp.simplify(qr.subs(r, 1))), ' kappa_c=', sp.simplify(((1 + qr.subs(r, 1)) / (1 - qr.subs(r, 1))) ** 2))
    ctx.note('g formula (rho^2-q^2)/(q(1+rho^2)) on F=0: ', sp.simplify(sp.numer(sp.together(shv_r / cc - (r ** 2 - q ** 2) / (q * (1 + r ** 2))))))
    ok = True
    for m in range(1, 13):
        am = g * (chm(m) - T(m))
        bm = B * U(m)
        xm = C * shm(m) - bm
        sub = {C: g * (r ** 2 - 1) / (r ** 2 + 1), B: g * (r ** 4 + r ** 2 + 1) / (r * (r ** 2 + 1)), c: cw}
        E = lambda n: chm(n) + 2 * cc ** 2 * sp.chebyshevt(n, cw) if n > 0 else 1 + 2 * cc ** 2
        d1 = sp.simplify(((am + xm) / g).subs(sub) - E(m + 1) / cc)
        d2 = sp.simplify(((am - xm) / g).subs(sub) - E(m - 1) / cc)
        ok = ok and d1 == 0 and (d2 == 0)
    ctx.note('E_n lemma m=1..12:', ctx.check(ok, 'base/base_check.py:47: ok'), '  E1,E2:', sp.simplify(E(1)), sp.simplify(E(2)))
    x = sp.Rational(3, 5)

    def ch_bounds(x, K=6):
        lo = sum((x ** (2 * k) / sp.factorial(2 * k) for k in range(K)))
        tail = x ** (2 * K) / sp.factorial(2 * K) / (1 - x ** 2 / ((2 * K + 1) * (2 * K + 2)))
        return (lo, lo + tail)

    def sh_bounds(x, K=6):
        lo = sum((x ** (2 * k + 1) / sp.factorial(2 * k + 1) for k in range(K)))
        tail = x ** (2 * K + 1) / sp.factorial(2 * K + 1) / (1 - x ** 2 / ((2 * K + 2) * (2 * K + 3)))
        return (lo, lo + tail)
    cl, cu = ch_bounds(x)
    sl, su = sh_bounds(x)
    ctx.note('ch(3/5) in [%s, %s], sh(3/5) in [%s, %s]' % (sp.N(cl, 12), sp.N(cu, 12), sp.N(sl, 12), sp.N(su, 12)))
    R = sp.Rational
    chk = {'1.1854 < ch(3/5) < 1.1855': cl > R(11854, 10000) and cu < R(11855, 10000), '0.6366 < sh(3/5) < 0.6367': sl > R(6366, 10000) and su < R(6367, 10000), '1.1854 > (1+sqrt13)/4  [(4*1.1854-1)^2 > 13]': (4 * R(11854, 10000) - 1) ** 2 > 13, 'S(3/5)=sh^2/t^2 < 1.13': su ** 2 / x ** 2 < R(113, 100), 'y(3/5) <= sh^2/(2 sqrt3) < 0.118  [sh^4 < 12*0.118^2]': su ** 4 < 12 * R(118, 1000) ** 2, 'sqrt(1-0.118^2) > 0.99': 1 - R(118, 1000) ** 2 > R(99, 100) ** 2, '1.186*1.13/(2*0.99) < 0.68': R(1186, 1000) * R(113, 100) / (2 * R(99, 100)) < R(68, 100), '0.36*1.13^2/(12*(1-0.118^2)) < 1/2': R(36, 100) * R(113, 100) ** 2 / (12 * (1 - R(118, 1000) ** 2)) < R(1, 2), '8-4*0.68-1.13>0': 8 - 4 * R(68, 100) - R(113, 100) > 0}
    for k, v in chk.items():
        ctx.note(k, ctx.check(bool(v), 'base/base_check.py:70: bool(v)'))
    ctx.check(ok, 'base/base_check.py:72: ok')
    ctx.check(all(chk.values()), 'base/base_check.py:73: all(chk.values())')
    ctx.check(True, 'derivation completed', kind='derivation')
