"""Exact reusable algebra, refactored from the supplied Part I computations.
See PROVENANCE.json for original source hashes.
"""
"""Exact-algebra helpers for hb_an/lower (sympy, rational arithmetic only; no floating point decides anything).

Field: rho > 0, q = q(rho) > 0 the positive root of the master curve
    F(rho,q) = rho^2(rho^2+1) - 2 q rho (rho^2-rho+1) - q^2 (rho^2+1) = 0      (F2).
Spiral: lam = rho e^{iw}, cos w = -rho/(1+rho^2)  (F1).  Symmetric functions of lam, mu = conj(lam):
    lam + mu = -2 rho^2/(1+rho^2),  lam*mu = rho^2.
Every real quantity below is a symmetric rational function of (lam, mu) with coefficients in Q(rho, q), hence an
element A(rho) + B(rho) q of Q(rho)[q]/(F).
"""
import sympy as sp
r, q, L, M = sp.symbols('rho q lam mu')
E1, E2 = sp.symbols('E1 E2')
e1 = -2 * r ** 2 / (1 + r ** 2)
e2 = r ** 2
Fq = r ** 2 * (r ** 2 + 1) - 2 * q * r * (r ** 2 - r + 1) - q ** 2 * (r ** 2 + 1)

def swap(z, extra=()):
    sub = {L: M, M: L}
    for a, b in extra:
        sub[a] = b
        sub[b] = a
    return z.subs(sub, simultaneous=True)

def _red_poly(p):
    """reduce polynomial in lam, mu modulo lam+mu=E1, lam*mu=E2; must give a polynomial without lam"""
    p = sp.expand(p.subs(M, E1 - L))
    P = sp.Poly(p, L)
    R = sp.rem(P, sp.Poly(L ** 2 - E1 * L + E2, L))
    c1 = sp.expand(R.coeff_monomial(L))
    c0 = sp.expand(R.coeff_monomial(1))
    return (c0, c1)

def symred(z):
    """z: rational in lam, mu, symmetric -> rational in rho, q (exact). Asserts symmetry."""
    z = sp.together(sp.expand(z))
    n, d = sp.fraction(z)
    n0, n1 = _red_poly(n)
    d0, d1 = _red_poly(d)
    num = sp.expand((n0 + n1 * L) * (d0 + d1 * (E1 - L)))
    num = sp.Poly(num, L)
    num = sp.rem(num, sp.Poly(L ** 2 - E1 * L + E2, L))
    c1 = sp.expand(num.coeff_monomial(L).subs({E1: e1, E2: e2}))
    if not sp.simplify(c1) == 0:
        raise ValueError('sp.simplify(c1) == 0')
    c0 = num.coeff_monomial(1)
    den = sp.expand(d0 ** 2 + d0 * d1 * E1 + d1 ** 2 * E2)
    return sp.together((c0 / den).subs({E1: e1, E2: e2}))

def Re(z):
    return symred((z + swap(z)) / 2)

def modF(z):
    """rational expression in rho, q -> (A, B) with z = A + B q on F = 0 (A, B rational in rho)"""
    z = sp.together(sp.expand(z))
    n, d = sp.fraction(z)

    def lin(p):
        P = sp.Poly(sp.expand(p), q)
        R = sp.rem(P, sp.Poly(Fq, q))
        return (sp.together(R.coeff_monomial(1)), sp.together(R.coeff_monomial(q)))
    na, nb = lin(n)
    da, db = lin(d)
    s1 = -2 * r * (r ** 2 - r + 1) / (r ** 2 + 1)
    p1 = -r ** 2
    num = sp.expand(na * da + na * db * (s1 - q) + nb * da * q + nb * db * p1)
    den = sp.together(da * da + da * db * s1 + db * db * p1)
    return (sp.factor(sp.together(num.coeff(q, 0) / den)), sp.factor(sp.together(num.coeff(q, 1) / den)))

def is_zero_modF(z):
    A, B = modF(z)
    return sp.simplify(A) == 0 and sp.simplify(B) == 0

def sturm_count(P, a, b):
    """number of distinct real roots of polynomial P (in rho) in [a,b], by an explicit Sturm sequence (exact)"""
    P = sp.Poly(P, r)
    if P.degree() <= 0:
        return 0
    P = sp.Poly(sp.quo(P, sp.gcd(P, P.diff(r))), r)
    seq = sp.sturm(P)

    def V(x):
        vals = [s.eval(x) for s in seq]
        vals = [v for v in vals if v != 0]
        return sum((1 for u, v in zip(vals, vals[1:]) if u * v < 0))
    cnt = V(a) - V(b)
    if P.eval(a) == 0:
        cnt += 1
    return cnt

def q_at(x):
    """q(x) = x [sqrt(Q) - (x^2-x+1)]/(x^2+1), returns (u, v, Q) with q = u + v sqrt(Q), all rational"""
    x = sp.Rational(x)
    Q = (x * x - x + 1) ** 2 + (x * x + 1) ** 2
    return (-x * (x * x - x + 1) / (x * x + 1), x / (x * x + 1), Q)

def sign_at(A, B, x):
    """exact sign of A(x) + B(x) q(x) at rational x"""
    u, v, Q = q_at(x)
    a = sp.together(sp.sympify(A).subs(r, x))
    b = sp.together(sp.sympify(B).subs(r, x))
    if not (a.is_Rational and b.is_Rational):
        raise ValueError('a.is_Rational and b.is_Rational')
    al = a + b * u
    be = b * v
    if be == 0:
        return sp.sign(al)
    if al == 0:
        return sp.sign(be)
    if sp.sign(al) == sp.sign(be):
        return sp.sign(al)
    return sp.sign(al) if al * al > be * be * Q else sp.sign(be) if al * al < be * be * Q else 0

def q_branches_at(x):
    u, v, Q = q_at(x)
    return ((u, v, Q), (u, -v, Q))

def _sign_lin(nA, nB, x, branch):
    """exact sign of nA(x) + nB(x) q_branch(x) at rational x (nA, nB polynomials in rho)"""
    u, v, Q = q_branches_at(x)[0 if branch == '+' else 1]
    a = sp.Rational(sp.sympify(nA).subs(r, x))
    b = sp.Rational(sp.sympify(nB).subs(r, x))
    al = a + b * u
    be = b * v
    if be == 0:
        return sp.sign(al)
    if al == 0:
        return sp.sign(be)
    if sp.sign(al) == sp.sign(be):
        return sp.sign(al)
    d = al * al - be * be * Q
    return sp.sign(al) if d > 0 else sp.sign(be) if d < 0 else 0

def certify_positive(z, a, b, name, verbose=False, collector=None):
    """Prove z(rho, q_+(rho)) > 0 for all rho in [a,b] (a<b rational); z rational in rho, q.
    z = (nA + nB q)/d on F = 0 with polynomials nA, nB, d in rho (exact reduction mod F).
    (i)   d has no root in [a,b]                                   (Sturm);
    (ii)  every root of G = f2 (nA+nB q_+)(nA+nB q_-) = f0 nB^2 - f1 nA nB + f2 nA^2 in [a,b] is simple and
          belongs to the branch q_- : on an exact isolating interval [l,u] of it, nA+nB q_- changes sign
          (then nA + nB q_+ does not vanish there, the root of G being simple);
    (iii) nA + nB q_+ and d have the same strict sign at one rational point.
    Hence nA + nB q_+ has no zero on [a,b] (its zeros are zeros of G of the + branch), and z > 0 on [a,b]."""
    a = sp.Rational(a)
    b = sp.Rational(b)
    A, B = modF(z)
    dA = sp.fraction(sp.together(A))[1]
    dB = sp.fraction(sp.together(B))[1]
    d = sp.lcm(sp.Poly(dA, r), sp.Poly(dB, r)).as_expr()
    nA = sp.expand(sp.cancel(A * d))
    nB = sp.expand(sp.cancel(B * d))
    if not (sp.fraction(sp.together(nA))[1].is_number and sp.fraction(sp.together(nB))[1].is_number):
        raise ValueError('sp.fraction(sp.together(nA))[1].is_number and sp.fraction(sp.together(nB))[1].is_number')
    f2 = -(r ** 2 + 1)
    f1 = -2 * r * (r ** 2 - r + 1)
    f0 = r ** 2 * (r ** 2 + 1)
    G = sp.Poly(sp.expand(f0 * nB ** 2 - f1 * nA * nB + f2 * nA ** 2), r, domain='QQ')
    cd = sturm_count(d, a, b)
    spurious = 0
    bad = 0
    if G.is_zero:
        raise ValueError('Zero norm does not certify strict positivity')
    if G.degree() > 0:
        for (l, u), mult in G.intervals(inf=a, sup=b):
            l = sp.Rational(l)
            u = sp.Rational(u)
            if mult != 1 or l == u:
                bad += 1
                continue
            sl = _sign_lin(nA, nB, l, '-')
            su = _sign_lin(nA, nB, u, '-')
            if sl * su < 0:
                spurious += 1
            else:
                bad += 1
    m = (a + b) / 2
    while G.eval(m) == 0:
        m = (m + b) / 2
    sg = _sign_lin(nA, nB, m, '+') * sp.sign(sp.Poly(d, r).eval(m))
    ok = cd == 0 and bad == 0 and (sg == 1)
    if collector is not None:
        collector.check(ok, name, kind="exact_quadratic_field_sign")
        collector.note({"id":name,"denominator_roots":cd,"spurious_norm_roots":spurious,
                        "invalid_norm_roots":bad,"midpoint_sign":str(sg)})
    return ok
