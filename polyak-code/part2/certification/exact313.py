"""Compact exact-3/13 numerical proposals, independent of proof consumers.

A scalar denominator-cleared Hermite compatibility equation replaces the
three nonlinear equations. All proposals are rational; no boolean outcome
or asserted real-number sign is exported.
"""
from fractions import Fraction
import mpmath as mp


def _rat(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def generate():
    with mp.workdps(100):
        u = mp.cos(6 * mp.pi / 13)
        v = mp.cos(4 * mp.pi / 13)

        def num(r, c):
            return (1 + c) * (1 - r * (8 * c ** 3 - 4 * c))

        def den(r, c):
            return 1 + 8 * r * c ** 2 * (1 + c)

        def nd(r, c):
            return 1 - r * (32 * c ** 3 + 24 * c ** 2 - 8 * c - 4)

        def dd(r, c):
            return 8 * r * c * (2 + 3 * c)

        def hn(r, c):
            return nd(r, c) * den(r, c) - num(r, c) * dd(r, c)

        def eq(r):
            du, dv = den(r, u), den(r, v)
            return ((u - v) * (hn(r, u) * dv ** 2 + hn(r, v) * du ** 2)
                    - 2 * (num(r, u) * dv - num(r, v) * du) * du * dv)

        r = mp.findroot(eq, (mp.mpf('0.1364'), mp.mpf('0.1365')))
        center = Fraction(mp.nstr(r, 45))
        inverse = Fraction(mp.nstr(1 / mp.diff(eq, r), 45))
        psi = lambda c: num(r, c) / den(r, c)
        slope = mp.diff(psi, u)
        quadratic = (psi(v)-psi(u)-slope*(v-u))/(v-u)**2
        linear = slope-2*quadratic*u
        constant = psi(u)-slope*u+quadratic*u*u
        secular = lambda d: (d+linear*linear/d
                             -2*(-quadratic-constant)-1/(d+2*quadratic))
        stable = mp.findroot(secular, (mp.mpf('6.3'), mp.mpf('6.5')))
        stable_center = Fraction(mp.nstr(stable, 35))
        stable_radius = Fraction(1, 10**10)
        normalized_u = mp.sqrt(stable/(stable+2*quadratic))
        u_center = Fraction(mp.nstr(normalized_u, 35))
        u_radius = Fraction(2, 10**9)
        return {
            'format': 'HEAVY_BALL_EXACT313_DATA',
            'version': 1,
            'scalar_root': {
                'center': _rat(center),
                'radius': _rat(Fraction(1, 10**15)),
                'preconditioner': _rat(inverse),
            },
            'stable_root': {'lower': _rat(stable_center-stable_radius),
                            'upper': _rat(stable_center+stable_radius)},
            'normalized_u': {'lower': _rat(u_center-u_radius),
                             'upper': _rat(u_center+u_radius)},
            'evaluation': {'precision': -256, 'taylor_depth': 64},
        }
