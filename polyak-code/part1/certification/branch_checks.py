"""Explicit interval sign checks; every acceptance is recorded.
The divided jet carries its own parameter, without shared mutable globals.
"""
import sympy as s
from flint import arb
from .interval import funcs
from .algebra.systems import G, u, c, z, h, A, B, y, P, D, w2, w3, L, U

def check_p1(Q, ctx):
    xv = z * z * B
    uv = 1 - z / 2 + z * z * A
    co = s.Poly(Q, c).all_coeffs()
    b2 = co[0]
    b1 = co[1] + 2 * xv * b2
    b0 = co[2] + 2 * xv * co[1] + 3 * xv * xv * b2
    raw = [-B, (s.expand(1 - xv * xv - uv * uv) / z).cancel(), b0.subs(u, uv), b1.subs(u, uv), s.Rational(1, 2) - z * A]
    fun = funcs(raw, (z, [A, B]))

    def check(zz, X, der):
        bneg, gz, q0, q1, positive = fun(zz, X)
        ctx.check(bneg > 0 and gz > arb('0.5') and (q0 - abs(q1) > 0) and (positive > 0), "regimes/branch_checks.py:14: bneg > 0 and gz > arb('0.5') and (q0 - abs(q1) > 0) and (positive > 0)")
        ctx.check(X[1] + zz * der[1] < 0, 'regimes/branch_checks.py:16: X[1] + zz * der[1] < 0')
        uz = -arb('0.5') + 2 * zz * X[0] + zz * zz * der[0]
        ctx.check(uz < 0, 'regimes/branch_checks.py:18: uz < 0')
        uv = 1 - zz / 2 + zz * zz * X[0]
        ctx.check(uz * uz * zz * zz * (1 - zz * zz) < 1 + uv * uv, 'regimes/branch_checks.py:20: uz * uz * zz * zz * (1 - zz * zz) < 1 + uv * uv')
    return check

def check_p2(vs, ctx):
    uv, xv, yv, pv, dv, W = vs
    subs = {u: uv}

    def mean(e):
        return (1 - pv) * e.subs(c, xv) + pv * e.subs(c, yv)
    e5 = mean(U(5)) - dv
    df = funcs([s.diff(e5, G)] + [s.diff(e5, v) for v in vs], (G, vs))

    def check(gv, X, der):
        uv, xv, yv, pv, dv, W = X
        ctx.check(uv > arb('.50') and uv < arb('.52') and (xv > -1) and (xv < 0) and (yv > 0) and (yv < 1), "regimes/branch_checks.py:31: uv > arb('.50') and uv < arb('.52') and (xv > -1) and (xv < 0) and (yv > 0) and (yv < 1)")
        ctx.check(W > 0 and W < 1 and (pv < 1), 'regimes/branch_checks.py:32: W > 0 and W < 1 and (pv < 1)')
        ctx.check(der[0] > 0 and der[0] < 1, 'regimes/branch_checks.py:33: der[0] > 0 and der[0] < 1')
        ctx.check(der[3] < 0, 'regimes/branch_checks.py:34: der[3] < 0')
        ds = df(gv, X)
        ctx.check(ds[0] + sum((ds[i + 1] * der[i] for i in range(6))) > 0, 'regimes/branch_checks.py:35: ds[0] + sum((ds[i + 1] * der[i] for i in range(6))) > 0')
        tt = gv.acosh()
        cc = [xv, yv]
        ww = [1 - pv, pv]
        gg = [1 - ci * ci - uv * uv for ci in cc]
        gbar = sum((ww[i] * gg[i] for i in range(2)))
        eta = gbar - abs(dv) / (gv * gv - 1).sqrt()
        ctx.check(eta > arb('.24'), "regimes/branch_checks.py:39: eta > arb('.24')")
        angles = [ci.acos() for ci in cc]
        for m in range(1, 16):
            aa = sum((ww[i] * gg[i] * ((m * tt).cosh() - (m * angles[i]).cos()) for i in range(2)))
            bb = sum((ww[i] * 2 * uv * (1 - cc[i] * cc[i]).sqrt() * (m * angles[i]).sin() for i in range(2)))
            rr = tt.sinh() / (m * tt).sinh()
            if m != 1:
                ctx.check((aa - bb) * rr + dv > 0, 'regimes/branch_checks.py:45: (aa - bb) * rr + dv > 0')
            if m not in (2, 3, 5):
                ctx.check((aa + bb) * rr - dv > 0, 'regimes/branch_checks.py:46: (aa + bb) * rr - dv > 0')
    return check

class Jet:
    """f(h)=a+h*b; the divided part is enclosed without dividing by h."""

    def __init__(self, a, b=0, parameter=0):
        self.parameter = arb(parameter)
        self.a = arb(a)
        self.b = arb(b)

    def __add__(self, o):
        if not isinstance(o, Jet):
            o = Jet(o, parameter=self.parameter)
        return Jet(self.a + o.a, self.b + o.b, self.parameter)
    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.a, -self.b, self.parameter)

    def __sub__(self, o):
        return self + -o if isinstance(o, Jet) else self + -o

    def __rsub__(self, o):
        return -self + o

    def __mul__(self, o):
        if not isinstance(o, Jet):
            o = Jet(o, parameter=self.parameter)
        return Jet(self.a * o.a, self.a * o.b + self.b * o.a + self.parameter * self.b * o.b, self.parameter)
    __rmul__ = __mul__

def check_central(Q, ctx):
    xv = -s.Rational(1, 2) + h * B
    uv = s.Rational(1, 2) + h * A
    co = s.Poly(Q, c).all_coeffs()
    a = -(xv + y)
    b = xv * y
    q2 = co[0]
    q1 = co[1] - 2 * a * q2
    q0 = co[2] - 2 * a * q1 - (a * a + 2 * b) * q2
    fq = funcs([e.subs({G: 1 + h, u: uv}) for e in (q2, q1, q0)], (h, [A, B, y, P, D, w2, w3]))
    tt = {m: [int(q) for q in s.Poly(s.cancel((s.chebyshevt(m, 1 + h) - 1) / h), h).all_coeffs()] for m in range(1, 24)}
    uu = {m: [int(q) for q in s.Poly(s.chebyshevu(m - 1, 1 + h), h).all_coeffs()] for m in range(1, 24)}

    def horner(co, x):
        v = arb(0)
        for a in co:
            v = v * x + a
        return v

    def check(hh, X, der):
        aa, bb, yy, pp, dd, ww2, ww3 = X
        uv = arb('.5') + hh * aa
        xx = -arb('.5') + hh * bb
        pv = hh * pp
        dv = hh * dd
        ctx.check(aa > 0 and aa < arb('.55') and (bb > -arb('0.27')) and (bb < 0), "regimes/branch_checks.py:81: aa > 0 and aa < arb('.55') and (bb > -arb('0.27')) and (bb < 0)")
        ctx.check(pp > 0 and pp < 3 and (dd > 0) and (dd < arb('2.2')), "regimes/branch_checks.py:82: pp > 0 and pp < 3 and (dd > 0) and (dd < arb('2.2'))")
        ctx.check(yy > arb('.23') and yy < arb('.29') and (ww2 > arb('.36')) and (ww2 < arb('.38')), "regimes/branch_checks.py:83: yy > arb('.23') and yy < arb('.29') and (ww2 > arb('.36')) and (ww2 < arb('.38'))")
        ctx.check(ww3 > arb('.59') and ww3 < arb('.65') and (der[5] + der[6] > 0), "regimes/branch_checks.py:84: ww3 > arb('.59') and ww3 < arb('.65') and (der[5] + der[6] > 0)")
        ctx.check(1 - ww2 - ww3 < arb('.031'), "regimes/branch_checks.py:85: 1 - ww2 - ww3 < arb('.031')")
        q2, q1, q0 = fq(hh, X)
        ctx.check(q0 - abs(q1) - abs(q2) > 0, 'regimes/branch_checks.py:86: q0 - abs(q1) - abs(q2) > 0')
        g1 = 1 - xx * xx - uv * uv
        g2 = 1 - yy * yy - uv * uv
        gb = (1 - pv) * g1 + pv * g2
        ctx.check(gb > arb('.49'), "regimes/branch_checks.py:88: gb > arb('.49')")
        ctx.check(gb - dd * (hh / (2 + hh)).nonnegative_part().sqrt() > arb('.25'), "regimes/branch_checks.py:89: gb - dd * (hh / (2 + hh)).nonnegative_part().sqrt() > arb('.25')")
        ctx.check(abs(bb) / (1 - xx * xx).sqrt() < arb(1) / 3, 'regimes/branch_checks.py:90: abs(bb) / (1 - xx * xx).sqrt() < arb(1) / 3')
        ctx.check(abs(bb - aa - hh * (bb * bb + aa * aa)) < 1, 'regimes/branch_checks.py:91: abs(bb - aa - hh * (bb * bb + aa * aa)) < 1')
        ctx.check(abs(bb - aa - hh * (bb * bb + aa * aa) + pp * (g2 - g1)) < 2, 'regimes/branch_checks.py:92: abs(bb - aa - hh * (bb * bb + aa * aa) + pp * (g2 - g1)) < 2')
        ctx.check(abs(aa + hh * der[0]) < 1, 'regimes/branch_checks.py:93: abs(aa + hh * der[0]) < 1')
        omega_sin = arb(3).sqrt() / 2
        hull = arb(-arb('.5') + hh * bb / 2, abs(hh * bb) / 2)
        delta_h = -bb / (1 - hull * hull).sqrt()
        delta = hh * delta_h
        jet = lambda a, b=0: Jet(a, b, hh)
        uj = jet(arb('.5'), aa)
        cj = jet(-arb('.5'), bb)
        gj = 1 - cj * cj - uj * uj
        sj = jet(omega_sin, (bb - hh * bb * bb) / ((1 - xx * xx).sqrt() + omega_sin))
        py = jet(0, pp)
        dj = jet(0, dd)
        a2 = yy.acos()
        s2 = (1 - yy * yy).sqrt()
        for m in range(1, 24):
            cm = arb(1) if m % 3 == 0 else -arb('.5')
            sm = arb(0) if m % 3 == 0 else omega_sin if m % 3 == 1 else -omega_sin
            md = m * delta
            mdh = m * delta_h
            cdiff = -mdh * mdh * hh / 2 * (md / 2).sinc() ** 2
            sdiff = mdh * md.sinc()
            cmj = jet(cm, cm * cdiff - sm * sdiff)
            smj = jet(sm, sm * cdiff + cm * sdiff)
            chj = jet(1, horner(tt[m], hh))
            um = horner(uu[m], hh)
            aj = (1 - py) * gj * (chj - cmj) + py * g2 * (chj - (m * a2).cos())
            bj = (1 - py) * 2 * uj * sj * smj + py * 2 * uj * s2 * (m * a2).sin()
            for sign in (-1, 1):
                if sign == -1 and m == 1 or (sign == 1 and m in (2, 3, 5)):
                    continue
                sl = aj + sign * bj - sign * dj * um
                critzero = m % 3 == 0 or (sign == -1 and m % 3 == 1) or (sign == 1 and m % 3 == 2)
                lower = sl.b if critzero else sl.b + arb(3) / 2 / arb(hh.upper())
                ctx.check(lower > 0, 'regimes/branch_checks.py:120: lower > 0')
    return check
