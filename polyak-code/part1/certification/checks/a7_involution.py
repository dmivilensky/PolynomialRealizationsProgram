"""Callable exact suite: struct/a7_involution.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
from ..algebra.waves import *

def run(ctx):
    t, v, w, C, m = sp.symbols('t v w C m', real=True)
    gg = sp.sin(w) ** 2 - sp.sinh(v) ** 2
    am = gg * (sp.cosh(m * t) - sp.cos(m * w))
    bm = 2 * sp.sinh(v) * sp.sin(w) * sp.sin(m * w)
    xm = C * sp.sinh(m * t) - bm
    iota = {t: -t, C: -C}
    ctx.note('(1) a_m(iota) - a_m      =', sp.simplify(am.subs(iota, simultaneous=True) - am))
    ctx.note('    x_m(iota) - x_m      =', sp.simplify(xm.subs(iota, simultaneous=True) - xm))
    ctx.note('    star |C|<=g: g unchanged, |C| unchanged (trivial)')
    qq = sp.symbols('qq', positive=True)
    lam = sp.exp(t + sp.I * w)
    s_orbit = (lam + qq ** 2 / lam) / (2 * qq)
    ctx.note("(1') s_orbit - ch(v+iw) at v=t-ln q:", sp.simplify((s_orbit - sp.cosh(t - sp.log(qq) + sp.I * w)).rewrite(sp.exp)))
    rho = sp.symbols('rho', positive=True)
    ctx.note('(2) F(1/rho,q/rho^2)*rho^6 - F(rho,q) =', sp.expand(F(1 / rho, q / rho ** 2) * rho ** 6 - F(rho, q)))
    ctx.note('    H_q(rho) - F(rho,q) =', sp.expand(H(rho, q) - F(rho, q)))
    ctx.note('(3) F(X,X/Y)*Y^2/X^2 - S =', sp.expand(F(X, X / Y) * Y ** 2 / X ** 2 - S))
    ctx.note('    S - 2Y(1+X^2)(shv - 1 + 1/(2 cht)) =', sp.simplify(S - 2 * Y * (1 + X ** 2) * (shv - 1 + 1 / (2 * chX(1)))))
    for mm in range(1, 8):
        for fn, nm in ((Lfun, 'L'), (Ufun, 'U')):
            e = fn(mm)
            ctx.check(sp.simplify(e.subs(X, 1 / X) - e) == 0, 'struct/a7_involution.py:32: sp.simplify(e.subs(X, 1 / X) - e) == 0')
    ctx.note('(4) L_m, U_m even in t (X->1/X) at fixed Y for m=1..7: OK  [general m: a_m, r_m even, b_m t-free]')
    Kt = sp.together(Lfun(1) + W * Ufun(2) + (1 - W) * Ufun(3))
    num, den = sp.fraction(sp.factor(Kt))
    R = sp.expand(num)
    ctx.note('(5) denominator of Kt:', sp.factor(den))
    ctx.note('    R(X,Y,c=ch t,W) =', sp.simplify(R.subs(c, chX(1))))
    ctx.note('    R(1/X)*X^k - R : k with identity:', [k for k in range(0, 20) if sp.expand(R.subs(X, 1 / X) * X ** k - R) == 0])
    for mm in range(1, 7):
        ctx.check(sp.simplify(Lfun(mm).subs(c, chX(1)) - 2 * shv * shX(1) ** 2) == 0, 'struct/a7_involution.py:43: sp.simplify(Lfun(mm).subs(c, chX(1)) - 2 * shv * shX(1) ** 2) == 0')
        ctx.check(sp.simplify(Ufun(mm).subs(c, chX(1)) + 2 * shv * shX(1) ** 2) == 0, 'struct/a7_involution.py:44: sp.simplify(Ufun(mm).subs(c, chX(1)) + 2 * shv * shX(1) ** 2) == 0')
    ctx.note('    L_m(c=ch t) = 2 sh v sh^2 t = -U_m(c=ch t), m=1..6: OK')
    for mm in range(1, 7):
        for cc in (1, -1):
            val = sp.simplify(Lfun(mm).subs(c, cc))
            val2 = sp.simplify(Ufun(mm).subs(c, cc))
            target = -shv ** 2 * r(mm) * (chX(mm) - cc ** mm)
            ctx.check(sp.simplify(val - target) == 0 and sp.simplify(val2 - target) == 0, 'struct/a7_involution.py:51: sp.simplify(val - target) == 0 and sp.simplify(val2 - target) == 0')
    ctx.note('(6) L_m(+-1) = U_m(+-1) = -sh^2 v * r_m (ch mt - (+-1)^m), m=1..6: OK')
    ctx.check(True, 'derivation completed', kind='derivation')
