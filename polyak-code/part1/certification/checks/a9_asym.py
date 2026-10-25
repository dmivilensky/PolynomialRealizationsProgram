"""Callable exact suite: struct/a9_asym.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
import mpmath as mpm

from ..precision import local_precision

@local_precision(bits=160,digits=40)
def run(ctx):
    t, u, e, k, z = sp.symbols('t u e k z')
    C = sp.symbols('C')
    mp_ = 4 * C ** 4 - 8 * C ** 2 + 4 * C - 1

    def red(expr):
        """reduce a rational function of C modulo the minimal polynomial (degree 4) -> cubic in C"""
        n, d = sp.fraction(sp.together(expr))
        n = sp.rem(sp.expand(n), mp_, C)
        d = sp.rem(sp.expand(d), mp_, C)
        s_, t_, g_ = sp.gcdex(d, mp_, C)
        ctx.check(sp.simplify(g_ - 1) == 0 or sp.degree(g_, C) == 0, 'struct/a9_asym.py:16: sp.simplify(g_ - 1) == 0 or sp.degree(g_, C) == 0')
        inv = sp.expand(s_ / g_)
        return sp.rem(sp.expand(n * inv), mp_, C)
    r, qv = sp.symbols('r qv')
    Fp = r ** 2 * (r ** 2 + 1) - 2 * qv * r * (r ** 2 - r + 1) - qv ** 2 * (r ** 2 + 1)
    mr = r ** 4 - 2 * r ** 3 + 2 * r ** 2 - 2 * r - 1

    def redr(expr):
        n, d = sp.fraction(sp.together(expr))
        n = sp.rem(sp.expand(n), mr, r)
        d = sp.rem(sp.expand(d), mr, r)
        s_, t_, g_ = sp.gcdex(d, mr, r)
        inv = sp.expand(s_ / g_)
        return sp.rem(sp.expand(n * inv), mr, r)
    Fr, Fq = (sp.diff(Fp, r), sp.diff(Fp, qv))
    Frr, Frq, Fqq = (sp.diff(Fp, r, 2), sp.diff(Fp, r, qv), sp.diff(Fp, qv, 2))
    at1 = lambda ex: ex.subs(qv, 1)
    ctx.note('F(r,1) - m(r) =', sp.expand(at1(Fp) - mr))
    ctx.note('F_r(rho_*,1) != 0: resultant(F_r, m) =', sp.resultant(at1(Fr), mr, r))
    rp = redr(-at1(Fq) / at1(Fr))
    rpp = redr(-(at1(Fqq) + 2 * at1(Frq) * rp + at1(Frr) * rp ** 2) / at1(Fr))
    c1r = redr(2 * rp)
    c2r = redr(2 * rpp + 2 * rp)
    ctx.note("rho'(1) =", rp)
    ctx.note('c1 in Q(rho_*):', c1r)
    ctx.note('c2 in Q(rho_*):', c2r)
    rho = red(C + (2 * C - 1) / (2 * C))
    ctx.note('rho_* in Q(c_*):', rho, ';  m(rho_*) mod =', red(rho ** 4 - 2 * rho ** 3 + 2 * rho ** 2 - 2 * rho - 1))
    c1 = red(c1r.subs(r, rho))
    c2 = red(c2r.subs(r, rho))
    ctx.note('c1 =', c1)
    ctx.note('c2 =', c2)
    cstar = [r_ for r_ in sp.Poly(mp_, C).real_roots() if r_ > 1][0]
    ctx.note('c_* =', sp.N(cstar, 25))
    ctx.note('c1 ~', sp.N(c1.subs(C, cstar), 25), '   c2 ~', sp.N(c2.subs(C, cstar), 25))
    for name, val in (('c1', c1), ('c2', c2)):
        P = sp.resultant(sp.Symbol('Z') - val, mp_, C)
        ctx.note('minimal polynomial of', name, ':', sp.factor(P))
    old = 2 * (2 * rho ** 3 + 2 * rho + 2) / (4 * rho ** 3 - 6 * rho ** 2 + 4 * rho - 2)
    ctx.note('c1 - 2*drho/dq|_{q=1} ([HB] formula) =', red(old - c1))
    for kap in (mpm.mpf(10) ** 6, mpm.mpf(10) ** 8):
        qq = (mpm.sqrt(kap) - 1) / (mpm.sqrt(kap) + 1)
        rr = mpm.findroot(lambda x: x ** 2 * (x ** 2 + 1) - 2 * qq * x * (x ** 2 - x + 1) - qq ** 2 * (x ** 2 + 1), 1.7)
        ee = 1 / mpm.sqrt(kap)
        rs = mpm.mpf(sp.N(rho.subs(C, cstar), 40))
        ctx.note('  kappa=%s: (rho - rho_* + c1 e)/e^2 =' % mpm.nstr(kap, 3), mpm.nstr((rr - rs + mpm.mpf(sp.N(c1.subs(C, cstar), 40)) * ee) / ee ** 2, 12))
    ctx.artifacts['asymptotics'] = {'c1': c1, 'c2': c2}
    ctx.note('\n(2) near kappa_c')
    tt, dd = sp.symbols('tt dd')
    Vt = sp.asinh(1 - 1 / (2 * sp.cosh(tt)))
    vser = sp.series(Vt, tt, 0, 5).removeO()
    ctx.note('V(t) =', vser, '  [even in t: V(-t)=V(t) exactly, since it depends on ch t]')
    v2 = sp.nsimplify(vser.coeff(tt, 2))
    phi = (1 + sp.sqrt(5)) / 2
    A = 1 / (phi ** 3 * 4 * phi ** 3)
    B = -sp.Rational(1, 2) / (phi ** 9 * 4 * phi ** 3) - 1 / (phi ** 3 * (4 * phi ** 3) ** 2)
    ctx.note('check sqrt(kc) = phi^3:', sp.simplify(phi ** 6 - (9 + 4 * sp.sqrt(5))), '; kc - 1 - 4phi^3:', sp.simplify(8 + 4 * sp.sqrt(5) - 4 * phi ** 3))
    a1 = sp.radsimp(sp.simplify(A))
    a2 = sp.radsimp(sp.simplify(B / 2 + (v2 + sp.Rational(1, 2)) * A ** 2))
    kc = 9 + 4 * sp.sqrt(5)
    ctx.note('rho - 1 = a1 (k-kc) + a2 (k-kc)^2 + O((k-kc)^3):  a1 =', a1, '=', sp.N(a1, 15), ' = 1/(4kc)?', ctx.check(sp.simplify(a1 - 1 / (4 * kc)) == 0, 'struct/a9_asym.py:77: sp.simplify(a1 - 1 / (4 * kc)) == 0'))
    ctx.note('   a2 =', a2, '=', sp.N(a2, 15))
    for dk in (mpm.mpf('1e-3'), mpm.mpf('-1e-3')):
        kk = mpm.mpf(sp.N(kc, 30)) + dk
        qq = (mpm.sqrt(kk) - 1) / (mpm.sqrt(kk) + 1)
        rr = mpm.findroot(lambda x: x ** 2 * (x ** 2 + 1) - 2 * qq * x * (x ** 2 - x + 1) - qq ** 2 * (x ** 2 + 1), 1.0)
        ctx.note('  dk=%s: (rho-1-a1 dk)/dk^2 =' % mpm.nstr(dk, 2), mpm.nstr((rr - 1 - mpm.mpf(sp.N(a1, 30)) * dk) / dk ** 2, 8))
    ctx.check(True, 'derivation completed', kind='derivation')
