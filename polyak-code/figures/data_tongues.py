"""Tongue functions kappa_{j/k} and the divergence boundary kappa_partial across the gap I_4
at fixed beta (data for the figure 'tongues').
Usage: python3 data_tongues.py BETA Y0 Y1 NY LMAX   (writes tongues_BETA.json)"""
import sys, json, numpy as np
from math import pi, cos, sin, tan
from fractions import Fraction
from multiprocessing import Pool
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbtools import xi_coeffs, PL_feasible

BETA = float(sys.argv[1]) if len(sys.argv) > 1 else 0.97
Y0, Y1, NY = (float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (1.36, 2.08, 181)
LMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 48

def kappa_jk(j, k, y, b):
    c0 = cos(2*pi*j/k); s0 = sin(2*pi*j/k); h0 = s0/tan(pi/k)
    den = (1-c0)*(y*(1+b)-2*(1-2*b*c0+b*b))-h0*y*(1-b)
    if den <= 0: return float('inf')
    return 1+((y-(1+b)*(1-c0))**2+(1-b)**2*s0**2)/den

def kappa_omega(y, b):
    """kappa on the boundary of Omega_1 at (alpha L, beta) = (y, b): the lag-one quadratic
    4b c^2 + 2(y-1-2b-b^2+b x)c + (2-2x+xy+2b^2-2by), x = y/kappa, has a double root in (-1,1)."""
    best = None
    # discriminant as a quadratic in x
    # B(x) = y-1-2b-b^2+b x ; C(x) = 2-2x+xy+2b^2-2by ; disc = B^2 - 4b C
    a2 = b*b; a1 = 2*b*(y-1-2*b-b*b)-4*b*(y-2); a0 = (y-1-2*b-b*b)**2-4*b*(2+2*b*b-2*b*y)
    disc = a1*a1-4*a2*a0
    if disc < 0: return None
    for x in [(-a1-disc**0.5)/(2*a2), (-a1+disc**0.5)/(2*a2)]:
        if 0 < x < y:
            c = -(y-1-2*b-b*b+b*x)/(4*b)
            if -1 < c < 1:
                kap = y/x
                if best is None or kap < best[0]: best = (kap, c)
    return best

def divergent(y, kap):
    X = xi_coeffs(kap, y, BETA)
    return any(PL_feasible(X, L, 0.0) for L in range(3, LMAX+1))

def kpartial(y):
    hi = min(kappa_jk(f.numerator, f.denominator, y, BETA) for f in FR_ALL)
    om = kappa_omega(y, BETA)
    lo = om[0] if om else 1.0+1e-9
    if not np.isfinite(hi):
        hi = 50.0
        if not divergent(y, hi): return None
    if divergent(y, lo): return lo
    for _ in range(26):
        m = 0.5*(lo+hi)
        if divergent(y, m): hi = m
        else: lo = m
    return hi

FR_ALL = sorted({Fraction(j, k) for k in range(3, LMAX+1) for j in range(1, k) if 2*j < k})
if __name__ == '__main__':
    ys = np.linspace(Y0, Y1, NY)
    with Pool(2) as p:
        kp = p.map(kpartial, ys)
    win = sorted({Fraction(j, k) for k in range(5, 61) for j in range(1, k) if Fraction(1, 5) <= Fraction(j, k) <= Fraction(1, 4)})
    yf = np.linspace(Y0, Y1, 1441)
    out = dict(beta=BETA, LMAX=LMAX, y=list(ys), kpartial=kp, yfine=list(yf),
               omega=[kappa_omega(y, BETA) for y in yf],
               tongues={f'{f.numerator}/{f.denominator}': [kappa_jk(f.numerator, f.denominator, y, BETA) for y in yf] for f in win})
    json.dump(out, open(f'tongues_{BETA}.json', 'w'))
    print('ok')
