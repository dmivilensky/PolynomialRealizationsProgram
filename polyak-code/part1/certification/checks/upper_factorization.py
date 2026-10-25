"""Callable exact suite: upper/upper_sym.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
import mpmath as mp

from ..precision import local_precision

@local_precision(bits=160,digits=40)
def run(ctx):
    X, Y, c, G, u, q = sp.symbols('X Y c G u q', positive=True)
    W2, W3, W5, W = sp.symbols('W2 W3 W5 W')

    def T(m, x):
        return sp.chebyshevt(m, x)

    def U(m, x):
        return sp.chebyshevu(m, x)

    def ok(e):
        ctx.check(sp.simplify(sp.together(e)) == 0, 'upper/upper_sym.py:11: sp.simplify(sp.together(e)) == 0')
        return True
    ctx.note('=== (S1) factorisation K = (G-c)(g*alpha - h*beta), general weights, lags {2,3,5}')
    Wd = {2: W2, 3: W3, 5: 1 - W2 - W3}
    chm = lambda m: (X ** m + X ** (-m)) / 2
    shm = lambda m: (X ** m - X ** (-m)) / 2
    shv = (Y - 1 / Y) / 2
    k = 1 - c ** 2
    gX = k - shv ** 2
    aX = lambda m: gX * (chm(m) - T(m, c))
    bX = lambda m: 2 * shv * k * U(m - 1, c)
    K_orig = aX(1) - bX(1) + sum((Wd[m] * shm(1) / shm(m) * (aX(m) + bX(m)) for m in Wd))

    def alpha_beta(Wd, G, c):
        al = 1 + sum((Wd[m] * sp.cancel((T(m, G) - T(m, c)) / (G - c)) / U(m - 1, G) for m in Wd))
        be = sum((Wd[m] * sp.cancel((U(m - 1, G) - U(m - 1, c)) / (G - c)) / U(m - 1, G) for m in Wd))
        return (al, be)
    al, be = alpha_beta(Wd, G, c)
    gG = k - u ** 2
    hG = 2 * u * k
    K_fact = (G - c) * (gG * al - hG * be)
    sub = {G: (X + 1 / X) / 2, u: shv}
    ctx.note('  identity holds:', ctx.check(ok(K_orig - K_fact.subs(sub)), 'upper/upper_sym.py:27: ok(K_orig - K_fact.subs(sub))'))
    ctx.note('  r_m = 1/U_{m-1}(ch t):', ctx.check(all((ok(shm(1) / shm(m) - 1 / U(m - 1, (X + 1 / X) / 2)) for m in (2, 3, 5))), 'upper/upper_sym.py:28: all((ok(shm(1) / shm(m) - 1 / U(m - 1, (X + 1 / X) / 2)) for m in (2, 3, 5)))'))
    al23, be23 = alpha_beta({2: W, 3: 1 - W}, G, c)
    N = W * (4 * G ** 2 - 1) + 4 * (1 - W) * G * (G + c)
    M = 8 * G ** 3 + 4 * G ** 2 * c - G + (1 - W) * (4 * G * c ** 2 - 3 * G) - W * (G + c)
    ctx.note('  lags {2,3}: alpha = M/(G(4G^2-1)), beta = N/(G(4G^2-1)):', ctx.check(ok(al23 - M / (G * (4 * G ** 2 - 1))), 'upper/upper_sym.py:33: ok(al23 - M / (G * (4 * G ** 2 - 1)))'), ctx.check(ok(be23 - N / (G * (4 * G ** 2 - 1))), 'upper/upper_sym.py:33: ok(be23 - N / (G * (4 * G ** 2 - 1)))'))
    ctx.note('=== (S2) master equation <=> u = 1 - 1/(2G)')
    H = X ** 4 - 2 * q * X ** 3 + (1 + 2 * q - q ** 2) * X ** 2 - 2 * q * X - q ** 2
    lhs = (X / q - q / X) / 2 - (1 - 1 / (X + 1 / X))
    ctx.note('  (Y-1/Y)/2 - 1 + 1/(2G) = H_q(X)/(2qX(X^2+1)) :', ctx.check(ok(lhs - H / (2 * q * X * (X ** 2 + 1))), 'upper/upper_sym.py:38: ok(lhs - H / (2 * q * X * (X ** 2 + 1)))'))
    ub = 1 - 1 / (2 * G)
    ck = -1 / (2 * G)
    ctx.note('  on the branch g = u/G at c = c_k:', ctx.check(ok(1 - ck ** 2 - ub ** 2 - ub / G), 'upper/upper_sym.py:40: ok(1 - ck ** 2 - ub ** 2 - ub / G)'))
    ctx.note('=== (S3) the tight weight W(G) and the rank condition D2 != D3')
    K23 = sp.together((G - c) * ((1 - c ** 2 - u ** 2) * al23 - 2 * u * (1 - c ** 2) * be23))
    Kb = sp.together(K23.subs(u, ub))
    ctx.note('  K(t_k, c_k) = 0 :', ctx.check(ok(Kb.subs(c, ck)), 'upper/upper_sym.py:45: ok(Kb.subs(c, ck))'))
    dK = sp.together(sp.diff(Kb, c).subs(c, ck))
    Wsol = sp.solve(sp.numer(dK), W)
    ctx.check(len(Wsol) == 1, 'upper/upper_sym.py:47: len(Wsol) == 1')
    WG = 2 * (1 + 2 * G - 2 * G ** 2) / (4 * G + 1)
    ctx.note('  W(G) = 2(1+2G-2G^2)/(4G+1) :', ctx.check(ok(Wsol[0] - WG), 'upper/upper_sym.py:49: ok(Wsol[0] - WG)'), ';  1-W = (4G^2-1)/(4G+1):', ctx.check(ok(1 - WG - (4 * G ** 2 - 1) / (4 * G + 1)), 'upper/upper_sym.py:49: ok(1 - WG - (4 * G ** 2 - 1) / (4 * G + 1))'))
    coefW = sp.together(sp.diff(K23, W))
    D23 = sp.factor(sp.together(sp.diff(coefW.subs(u, ub), c).subs(c, ck)))
    ctx.note('  d/dc (r2F2 - r3F3) at the branch point =', D23)
    ctx.note('  [so D2 - D3 = -sin(w_k) * that, nonzero for G >= 1]')
    ctx.note('=== (S4) K(t_k, c) = -(G-c)(2Gc+1)^2 Q(c) / (2 G^3 (4G+1)),  Q = 2Gc^2-(2G-1)c+4G(G-1)')
    Q = 2 * G * c ** 2 - (2 * G - 1) * c + 4 * G * (G - 1)
    ctx.note('  identity:', ctx.check(ok(Kb.subs(W, WG) + (G - c) * (2 * G * c + 1) ** 2 * Q / (2 * G ** 3 * (4 * G + 1))), 'upper/upper_sym.py:58: ok(Kb.subs(W, WG) + (G - c) * (2 * G * c + 1) ** 2 * Q / (2 * G ** 3 * (4 * G + 1)))'))
    p1 = 32 * G ** 3 - 36 * G ** 2 + 4 * G - 1
    ctx.note('  disc_c Q = -p1(G):', ctx.check(ok(sp.discriminant(Q, c) + p1), 'upper/upper_sym.py:60: ok(sp.discriminant(Q, c) + p1)'), '; Q(c_v) = p1/(8G), c_v=(2G-1)/(4G):', ctx.check(ok(Q.subs(c, (2 * G - 1) / (4 * G)) - p1 / (8 * G)), 'upper/upper_sym.py:60: ok(Q.subs(c, (2 * G - 1) / (4 * G)) - p1 / (8 * G))'))
    ctx.note('  Q(0) = 4G(G-1), Q(1) = (2G-1)^2, Q(-1) =', sp.factor(Q.subs(c, -1)))
    ctx.note('=== (S5) roots: p1 and 2G^2-2G-1')
    P1 = sp.Poly(p1, G)
    ctx.note('  real roots of p1 (exact count via Sturm):', sp.Poly(p1, G).count_roots(), ' isolating:', P1.intervals(eps=sp.Rational(1, 10 ** 12)))
    ctx.note('  p1(1) =', p1.subs(G, 1), ';  G_W = (1+sqrt3)/2 root of 2G^2-2G-1;  G_W^2 < 2 :', ctx.check(sp.simplify(((1 + sp.sqrt(3)) / 2) ** 2 - 2) < 0, 'upper/upper_sym.py:66: sp.simplify(((1 + sp.sqrt(3)) / 2) ** 2 - 2) < 0'))
    ctx.note('=== (S6) minimal polynomials of rho, q, kappa at the thresholds')
    kap = sp.symbols('kappa')
    Hq = sp.Poly(H.subs(X, sp.Symbol('r')), sp.Symbol('r'))
    r = sp.Symbol('r')

    def minpolys(polyG, name, numerics):
        pr = sp.factor(sp.numer(sp.together(polyG.subs(G, (r + 1 / r) / 2))))
        pq = sp.factor(sp.resultant(sp.Poly(pr, r).as_expr(), H.subs(X, r), r))
        pk = sp.factor(sp.resultant(sp.Poly(pq, q).as_expr(), kap * (1 - q) ** 2 - (1 + q) ** 2, q))
        ctx.note('  [%s] rho:' % name, pr)
        ctx.note('        q  :', pq)
        ctx.note('        kappa:', pk)
        ctx.note('        number of irreducible factors (rho, q, kappa):', [len(sp.factor_list(e)[1]) for e in (pr, pq, pk)])
        for val in numerics:
            for fac, _ in sp.factor_list(pk)[1]:
                if abs(sp.N(fac.subs(kap, val), 30)) < 1e-12 * max(1, abs(sp.N(sp.diff(fac, kap).subs(kap, val)))):
                    ctx.note('        kappa = %s is a root of %s ; derivative there %s' % (sp.N(val, 20), fac, sp.N(sp.diff(fac, kap).subs(kap, val), 6)))

    def kap_of(Gv, sgn):
        t = sgn * mp.acosh(Gv)
        uu = 1 - 1 / (2 * Gv)
        qq = mp.e ** (t - mp.asinh(uu))
        return ((1 + qq) / (1 - qq)) ** 2
    GWv = (1 + mp.sqrt(3)) / 2
    G1v = mp.findroot(lambda x: 32 * x ** 3 - 36 * x ** 2 + 4 * x - 1, 1.03)
    kW, k1, k2 = (kap_of(GWv, -1), kap_of(G1v, -1), kap_of(G1v, 1))
    ctx.note('  numerics: kappa_W = %s, kappa_1 = %s, kappa_2 = %s' % (mp.nstr(kW, 25), mp.nstr(k1, 25), mp.nstr(k2, 25)))
    minpolys(2 * G ** 2 - 2 * G - 1, 'kappa_W', [sp.Float(str(kW), 40)])
    minpolys(p1, 'kappa_1,2', [sp.Float(str(k1), 40), sp.Float(str(k2), 40)])
    ctx.note('=== (S7) auxiliary exact facts')
    ctx.note('  p1(26/25) =', p1.subs(G, sp.Rational(26, 25)), " (>0);  p1'(G) = 96G^2-72G+4 >= 28 for G >= 1")
    cs_ = sp.Poly(4 * G ** 4 - 8 * G ** 2 + 4 * G - 1, G)
    iv = [I for I in cs_.intervals(eps=sp.Rational(1, 10 ** 9)) if I[0][0] > 1]
    ctx.note('  c_* (root > 1 of 4c^4-8c^2+4c-1) in', iv, '; G_1 < 26/25 < c_* < 23/20 < G_W:', ctx.check(iv[0][0][0] > sp.Rational(26, 25), 'upper/upper_sym.py:97: iv[0][0][0] > sp.Rational(26, 25)'), ctx.check(iv[0][0][1] < sp.Rational(23, 20), 'upper/upper_sym.py:97: iv[0][0][1] < sp.Rational(23, 20)'), ctx.check(sp.Rational(23, 20) < (1 + sp.sqrt(3)) / 2, 'upper/upper_sym.py:97: sp.Rational(23, 20) < (1 + sp.sqrt(3)) / 2'))
    r_ = sp.Symbol('rho', positive=True)
    ctx.note('  W in rho:', sp.factor(sp.together(WG.subs(G, (r_ + 1 / r_) / 2))), ';  1-W:', sp.factor(sp.together((1 - WG).subs(G, (r_ + 1 / r_) / 2))))
    ctx.note('  kappa >= 3+2sqrt2 <=> q >= sqrt2-1 <=> t_max >= 0 :', ctx.check(sp.simplify(((1 + (sp.sqrt(2) - 1)) / (1 - (sp.sqrt(2) - 1))) ** 2 - (3 + 2 * sp.sqrt(2))) == 0, 'upper/upper_sym.py:101: sp.simplify(((1 + (sp.sqrt(2) - 1)) / (1 - (sp.sqrt(2) - 1))) ** 2 - (3 + 2 * sp.sqrt(2))) == 0'))
    ctx.note('  closed forms sqrt(kappa) = coth((v-t)/2):')
    co = lambda x: mp.cosh(x) / mp.sinh(x)
    ctx.note('    kappa_W:', mp.nstr(co((mp.asinh((3 - mp.sqrt(3)) / 2) + mp.acosh(GWv)) / 2) ** 2, 25))
    ctx.note('    kappa_1:', mp.nstr(co((mp.asinh(1 - 1 / (2 * G1v)) + mp.acosh(G1v)) / 2) ** 2, 25))
    ctx.note('    kappa_2:', mp.nstr(co((mp.asinh(1 - 1 / (2 * G1v)) - mp.acosh(G1v)) / 2) ** 2, 25))
    phi = (1 + sp.sqrt(5)) / 2
    ctx.note('    kappa_c = coth^2(asinh(1/2)/2) = phi^6 = 9+4sqrt5:', ctx.check(sp.simplify(sp.expand(phi ** 6) - 9 - 4 * sp.sqrt(5)) == 0, 'upper/upper_sym.py:108: sp.simplify(sp.expand(phi ** 6) - 9 - 4 * sp.sqrt(5)) == 0'), ctx.check(sp.simplify(sp.exp(sp.asinh(sp.Rational(1, 2))) - phi) == 0, 'upper/upper_sym.py:108: sp.simplify(sp.exp(sp.asinh(sp.Rational(1, 2))) - phi) == 0'))
    ctx.check(True, 'derivation completed', kind='derivation')
