"""Callable exact suite: lower/a3_regions.py. No file caches or implicit execution.
Algebraic source attribution: PROVENANCE.json.
"""
import sympy as sp
from ..algebra.quadratic import *

def run(ctx):
    lam, mu = (L, M)
    s = (lam + q ** 2 / lam) / (2 * q)
    sb = swap(s)
    g = 2 * r * (r ** 2 - r + 1) / (r ** 2 + 1) ** 2
    c = (r + 1 / r) / 2
    C = g * (r ** 2 - 1) / (r ** 2 + 1)
    Dl = q / 2 * (1 - 1 / lam)
    Dlb = swap(Dl)
    alp = Dlb * (s + 1) / 2
    alm = Dlb * (s - 1) / 2
    em = mu / r
    ep = lam / r
    a_m = g / (4 * c * r)
    a_p = g * r / (4 * c)
    b_m = g * c * em + alp
    b_p = g * c * ep + alm
    gam_m = symred(g * r / (4 * c) - (alp + swap(alp)) / 2 - Dl * Dlb / 4)
    gam_p = symred(g / (4 * c * r) - (alm + swap(alm)) / 2 - Dl * Dlb / 4)
    nb2_m = Re(b_m * swap(b_m))
    nb2_p = Re(b_p * swap(b_p))
    A0 = (1 - q ** 4) ** 2
    R = sp.Rational
    ok_all = True

    def cert(z, a, b, nm):
        nonlocal ok_all
        ok_all &= certify_positive(z, a, b, nm, collector=ctx)
    ctx.note('== endpoints ==')
    q2 = 3 - 2 * sp.sqrt(2)
    x = R(33, 100)
    H = x ** 4 - 2 * q2 * x ** 3 + (1 + 2 * q2 - q2 ** 2) * x ** 2 - 2 * q2 * x - q2 ** 2
    Hs = sp.expand(H)
    a_, b_ = Hs.as_independent(sp.sqrt(2))
    b_ = sp.expand(b_ / sp.sqrt(2))
    sgn = sp.sign(a_) if sp.sign(a_) == sp.sign(b_) else sp.sign(a_) if a_ ** 2 > 2 * b_ ** 2 else sp.sign(b_)
    ctx.note('  H_{q(2)}(33/100) = %s + %s sqrt2, sign %s  => rho(2) > 33/100: %s' % (a_, b_, sgn, sgn == -1))
    ok_all &= sgn == -1
    Pst = lambda y: y ** 4 - 2 * y ** 3 + 2 * y ** 2 - 2 * y - 1
    ctx.note('  P_*(1713/1000) = %s > 0, P_*(1) = %s < 0 => 1 < rho_* < 1713/1000: %s' % (Pst(R(1713, 1000)), Pst(1), Pst(R(1713, 1000)) > 0))
    ok_all &= Pst(R(1713, 1000)) > 0
    ctx.note('== Region I: rho in [33/100, 1]  (kappa in [2, kappa_c]) ==')
    for nm, gm, nb2 in [('-', gam_m, nb2_m), ('+', gam_p, nb2_p)]:
        cert(gm + A0, R(33, 100), 1, 'I%s.a  gamma%s + A0 > 0' % (nm, nm))
        cert((gm + A0) ** 2 - nb2, R(33, 100), 1, 'I%s.b  (gamma%s + A0)^2 - |beta%s|^2 > 0' % (nm, nm, nm))
    ctx.note('== Region II: rho in [1, 6/5] ==')
    epsb = R(3, 40) * (r ** 2 - 1) * (r + 1) ** 2 / (r * (r ** 2 + 1))
    for nm, nb2 in [('-', nb2_m), ('+', nb2_p)]:
        cert(1 - nb2, 1, R(6, 5), 'II0%s  1 - |beta%s|^2 > 0' % (nm, nm))
    choice = {('-', 0): 'V', ('-', 1): 'V', ('-', 2): 'D', ('+', 0): 'D', ('+', 1): 'D', ('+', 2): 'V'}
    for nm, a, b, gm in [('-', a_m, b_m, gam_m), ('+', a_p, b_p, gam_p)]:
        A2 = a - epsb
        cert(A2, 1, R(6, 5), 'II%s  A2 = a%s - epsbar > 0' % (nm, nm))
        for rr in range(3):
            Br = Re(b * ep ** rr)
            B2 = Br + epsb
            C2 = gm + A0
            cert(A2 + B2 + C2, 1, R(6, 5), 'II%s,r=%d  P(1) > 0' % (nm, rr))
            if choice[nm, rr] == 'V':
                cert(2 * A2 + B2, 1, R(6, 5), "II%s,r=%d  P'(1) = 2A2+B2 > 0" % (nm, rr))
            else:
                cert(4 * A2 * C2 - B2 ** 2, 1, R(6, 5), 'II%s,r=%d  4A2C2 - B2^2 > 0' % (nm, rr))
    ctx.note('== Region III: rho in [6/5, 1713/1000] ==')
    K0 = 10
    X10 = r ** K0
    for nm, a, gm, nb2 in [('-', a_m, gam_m, nb2_m), ('+', a_p, gam_p, nb2_p)]:
        cert(4 * a ** 2 * X10 ** 2 - nb2, R(6, 5), R(1713, 1000), 'III%s.tail1  (2a rho^10)^2 - |beta|^2 > 0' % nm)
        Y = a * X10 ** 2 + gm + A0
        cert(Y, R(6, 5), R(1713, 1000), 'III%s.tail2  a rho^20 + gamma + A0 > 0' % nm)
        cert(Y ** 2 - nb2 * X10 ** 2, R(6, 5), R(1713, 1000), 'III%s.tail3  (a rho^20+gamma+A0)^2 - |beta|^2 rho^20 > 0' % nm)
    cpsi = (C + 2 * Re(s)) / 4
    sig0 = s + Dl
    sig0b = swap(sig0)
    for k in range(1, K0):
        Nk = lam ** k
        Nkb = mu ** k
        Tk = cpsi * r ** (2 * k) - cpsi - symred(((sig0b + sb * Nkb) * (Nk - 1) + (sig0 + s * Nk) * (Nkb - 1)) / 4)
        yk = 2 * (-q ** 2) ** ((k + 1) // 2)
        Rk = symred(((Nk - 1) * (Nkb - 1) - (s * Nk - sig0) * (sb * Nkb - sig0b)) / 4) + (yk - 2) ** 2 / 4
        cert(Rk - Tk, R(6, 5), R(1713, 1000), 'III.k=%d  R-T > 0' % k)
        cert(Rk + Tk, R(6, 5), R(1713, 1000), 'III.k=%d  R+T > 0' % k)
    ctx.note('ALL PROVED' if ok_all else 'SOME FAILED')
    ctx.check(ok_all, 'lower/a3_regions.py:85: ok_all')
    ctx.check(True, 'derivation completed', kind='derivation')
