"""Proposition 9.10: verification with exact rational data,
exact algebraic comparisons and outward-rounded ball arithmetic (Arb via python-flint, 200 bits).

Checks:
  (1) the lag-one quadratic of the tuning has the printed exact coefficients, is positive at c=0 and
      at c=cos(2pi/5) and negative at its vertex, which lies in (0, cos(2pi/5)): the tuning lies in I_4;
  (2) Theta > pi/6 on (0, pi]: on each of 4000 intervals covering [-1,1], Xi(c) <= 0 or
      Xi(c) < cot(pi/6) sqrt(1-c^2);
  (3) the spectrum nu = (149/797) delta_{2*2pi/13} + (648/797) delta_{3*2pi/13}, C = 0, is feasible at t=0:
      lower and upper lag slacks (3.6) at least 3.8594e-4 for m = 1,...,12, and g_bar in (0.79908, 0.79909).

Usage: python3 prop13_check.py
"""
import sys
from flint import arb, acb, fmpq, ctx
from sympy import Rational as Q, symbols, expand, cos as scos, pi as spi, nsimplify, Poly, simplify

ctx.prec = 200
PI = arb.pi()
KAPPA, Y, BETA = fmpq(100), fmpq(70471, 31800), fmpq(6169, 9900)

def fail(*msg):
    print('CHECK FAILED', *msg); sys.exit(1)

# (1) exact gap membership
c = symbols('c')
k_, y_, b_ = Q(100), Q(70471, 31800), Q(6169, 9900)
x_ = y_/k_
Lc = expand(4*b_*c**2+2*(y_-1-2*b_-b_**2+b_*x_)*c+(2-2*x_+x_*y_+2*b_**2-2*b_*y_))
printed = (274486940640000*c**2-89129341428596*c+2155051415249)/Q(110124036000000)
if expand(Lc-printed) != 0: fail('lag-one quadratic differs from the printed one')
c5 = nsimplify(scos(2*spi/5))
a2, a1, a0 = Poly(Lc, c).all_coeffs(); v = -a1/(2*a2)
if not (Lc.subs(c, 0) > 0 and simplify(Lc.subs(c, c5)) > 0 and Lc.subs(c, v) < 0 and v > 0 and simplify(c5-v) > 0):
    fail('gap membership')
print('(1) lag-one quadratic as printed; positive at 0 and cos(2pi/5), negative at the vertex in (0, cos(2pi/5)): tuning in I_4')

# (2) Theta > pi/6
x = arb(KAPPA); y = arb(Y); b = arb(BETA)
xx = y/x
A = 1+b-(xx+y)/2; B = (y-xx)/2; den = 2*B*(1-b)
X0, X1, X2 = (B*B-(1-b)**2-A*A)/den, 2*A*(1+b)/den, -4*b/den
sqrt3 = arb(3).sqrt()
N = 4000
for i in range(N):
    lo = arb(-1)+arb(2)*i/N; hi = arb(-1)+arb(2)*(i+1)/N
    I = lo.union(hi)
    Xi = X0+X1*I+X2*I*I
    if Xi.upper() <= 0: continue
    s = (1-I*I)
    s = arb(0).union(s) if not (s > 0) else s
    rhs = sqrt3*s.sqrt() if s > 0 else None
    if rhs is None or not (Xi < rhs): fail('Theta > pi/6 on interval', i)
print('(2) Theta > pi/6 on (0, pi]: verified on 4000 intervals')

# (3) spectral slacks at t = 0
W = {2: fmpq(149, 797), 3: fmpq(648, 797)}
def wave(j):
    w = 2*PI*j/13
    z = acb(w.cos(), w.sin())
    m = (z+b/z-A)/B
    g = 1-abs(m)**2
    return w, g, m.imag
gbar = sum(arb(W[j])*wave(j)[1] for j in W)
lows = []
for mm in range(1, 13):
    am = sum(arb(W[j])*wave(j)[1]*(1-(mm*wave(j)[0]).cos()) for j in W)
    bm = sum(arb(W[j])*2*wave(j)[2]*(mm*wave(j)[0]).sin() for j in W)
    lows += [am-bm, am+bm]
mn = min(lows, key=lambda v: v.lower())
if not all(v > arb('3.8594e-4') for v in lows): fail('lag slacks')
if not (gbar > arb('0.79908') and gbar < arb('0.79909')): fail('g_bar')
print('(3) min lag slack =', mn.str(8), '; g_bar =', gbar.str(10))
print('RESULT: Proposition 9.10 VERIFIED')
