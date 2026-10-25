"""Rational three-dimensional contact-system proposals in quadratic coefficients."""
from fractions import Fraction
import mpmath as mp


def q(value):
    value = Fraction(value)
    return [value.numerator, value.denominator]


def build_payload():
    with mp.workdps(100):
        u, v = mp.cos(6*mp.pi/13), mp.cos(4*mp.pi/13)

        def w(c): return 8*c*c*(1+c)
        def wd(c): return 8*c*(2+3*c)
        def z(c): return 8*c**3-4*c
        def zd(c): return 24*c*c-4
        def psi(r,c): return (1+c)*(1-r*z(c))/(1+r*w(c))
        def psid(r,c): return mp.diff(lambda t: psi(r,t),c)
        def compatibility(r):
            return (u-v)*(psid(r,u)+psid(r,v))-2*(psi(r,u)-psi(r,v))
        r=mp.findroot(compatibility, ('0.1364','0.1365'))
        a=((psi(r,v)-psi(r,u))/(v-u)-psid(r,u))/(v-u)
        b=psid(r,u)-2*a*u
        d=psi(r,u)-u*psid(r,u)+a*u*u
        center=mp.matrix([d,b,a])

        def system(d,b,a):
            def xi(c): return d+b*c+a*c*c
            def xid(c): return b+2*a*c
            num=1+u-xi(u)
            den=xi(u)*w(u)+(1+u)*z(u)
            def value(c): return den*(xi(c)-1-c)+num*(xi(c)*w(c)+(1+c)*z(c))
            def slope(c): return den*(xid(c)-1)+num*(xid(c)*w(c)+xi(c)*wd(c)+z(c)+(1+c)*zd(c))
            return mp.matrix([value(v),slope(u),slope(v)])
        jacobian=mp.matrix([[mp.diff(lambda t: system(*(list(center)[:j]+[t]+list(center)[j+1:]))[i],center[j])
                             for j in range(3)] for i in range(3)])
        inverse=jacobian**-1
        return {'schema':'heavy-ball-exact313-system-v1',
                'center':[q(mp.nstr(x,40)) for x in center],
                'radius':[q(Fraction(1,10**8)) for _ in range(3)],
                'preconditioner':[[q(mp.nstr(inverse[i,j],32)) for j in range(3)] for i in range(3)],
                'precision':-192,'taylor_depth':40}
