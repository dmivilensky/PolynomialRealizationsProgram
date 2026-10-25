"""Proposition 9.11 and the tuning (100, 113/50, 3/5) of [Wang 2026]:
exact rational verification that the tuning lies in the gap I_4 and that the two-lag
inequality (9.8) holds on [-1,1] (Sturm sequences, exact arithmetic).

Usage: python3 convgap_check.py
"""
from sympy import Rational as Q, symbols, expand, Poly, chebyshevt, chebyshevu, cos, pi, sqrt, nsimplify, real_roots, simplify

c = symbols('c')

def Xi(kappa, y, beta):
    """The quadratic Xi of Lemma 6.2 (6.4), exact."""
    x = y/kappa
    A = 1+beta-(x+y)/2
    B = (y-x)/2
    den = 2*B*(1-beta)
    return expand((B*B-(1-beta)**2-A*A+2*A*(1+beta)*c-4*beta*c**2)/den)

def lag_one_quadratic(kappa, y, beta):
    """The lag-one quadratic (6.6)."""
    x = y/kappa
    return expand(4*beta*c**2+2*(y-1-2*beta-beta**2+beta*x)*c+(2-2*x+x*y+2*beta**2-2*beta*y))

def in_gap(kappa, y, beta, K):
    """Tuning in I_K: the lag-one quadratic is positive at cos(2pi/K), cos(2pi/(K+1)) and negative at
    its vertex, which lies between them (Proposition 8.12)."""
    Lc = lag_one_quadratic(kappa, y, beta)
    cK = nsimplify(cos(2*pi/K)); cK1 = nsimplify(cos(2*pi/(K+1)))
    p = Poly(Lc, c); a2, a1, a0 = p.all_coeffs()
    v = -a1/(2*a2)
    ok = simplify(Lc.subs(c, cK)) > 0 and simplify(Lc.subs(c, cK1)) > 0 and simplify(Lc.subs(c, v)) < 0 \
        and simplify(v-cK) > 0 and simplify(cK1-v) > 0
    return bool(ok), Lc

def twolag_poly(kappa, y, beta, K, r, gamma):
    X = Xi(kappa, y, beta)
    return expand((1-c**2)*(1-r*chebyshevu(K-1, c))-X*((1-c)+r*(1-chebyshevt(K, c))+gamma))

def check(name, kappa, y, beta, K, r, gamma, expect=None):
    ok_gap, Lc = in_gap(kappa, y, beta, K)
    P = twolag_poly(kappa, y, beta, K, r, gamma)
    nroots = Poly(P, c).count_roots(-1, 1)
    pos = P.subs(c, 0) > 0
    print(f'{name}: Xi = {Xi(kappa, y, beta)}')
    print(f'   lag-one quadratic = {Lc}')
    print(f'   in I_{K}: {ok_gap}')
    print(f'   two-lag polynomial P(c) = {P}')
    print(f'   real roots of P in [-1,1]: {nroots};  P(0) = {P.subs(c, 0)}')
    match = True
    if expect is not None:
        match = expand(P-expect) == 0
        print('   matches the polynomial printed in the proof:', match)
    res = ok_gap and nroots == 0 and pos and match
    print('   RESULT:', 'VERIFIED' if res else 'FAILED')
    return res

if __name__ == '__main__':
    expect = (-Q(644800, 208791)*c**6+Q(23608, 7733)*c**5+Q(389324, 94905)*c**4-Q(34149683, 5219775)*c**3
              + Q(1007042, 347985)*c**2-Q(92371789, 208791000)*c+Q(45613, 1898100))
    r1 = check('Proposition 9.11 (kappa=100, alpha L=111/50, beta=31/50; r=13/100, gamma=1/1000)',
               Q(100), Q(111, 50), Q(31, 50), 4, Q(13, 100), Q(1, 1000), expect)
    r2 = check('tuning of [Wang 2026] (kappa=100, alpha L=113/50, beta=3/5; r=4/25, gamma=1/100000)',
               Q(100), Q(113, 50), Q(3, 5), 4, Q(4, 25), Q(1, 100000))
    raise SystemExit(0 if (r1 and r2) else 1)
