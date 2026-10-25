"""Data for the figure 'staircase': the boundary of the divergence set across the gap I_4 at fixed kappa,
located by bisection in alpha L with the periodic programs of period at most 120, and the heaviest atom of the
program with the least threshold.
Usage: python3 data_staircase.py KAPPA BETA0 BETA1 NBETA OUT"""
import sys, json, numpy as np
from math import pi, cos
from scipy.optimize import brentq
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbtools import *

LMAX = 120
LS = list(range(9, LMAX+1))

def Lcal(c, y, beta, kappa):
    x = y/kappa
    return 4*beta*c*c+2*(y-1-2*beta-beta**2+beta*x)*c+(2-2*x+x*y+2*beta**2-2*beta*y)

def tangency(beta, kappa):
    # alpha L on boundary of Omega_1: min over c in [-1,1] of L(c) = 0
    def m(y):
        cs = np.linspace(-1, 1, 4001); v = Lcal(cs, y, beta, kappa); i = np.argmin(v)
        lo, hi = cs[max(i-1, 0)], cs[min(i+1, 4000)]
        for _ in range(60):
            a1 = lo+(hi-lo)/3; a2 = hi-(hi-lo)/3
            if Lcal(a1, y, beta, kappa) < Lcal(a2, y, beta, kappa): hi = a2
            else: lo = a1
        return Lcal(0.5*(lo+hi), y, beta, kappa), 0.5*(lo+hi)
    ys = np.linspace(0.5, 2*(1+beta)-1e-6, 2000)
    vals = [m(y)[0] for y in ys]
    for i in range(len(ys)-1):
        if vals[i] > 0 and vals[i+1] <= 0:
            y0 = brentq(lambda y: m(y)[0], ys[i], ys[i+1], xtol=1e-14)
            return y0, m(y0)[1]
    return None, None

def tongue_y(K, beta, kappa):
    c = cos(2*pi/K)
    ys = np.linspace(0.5, 2*(1+beta)-1e-6, 4000)
    v = Lcal(c, ys, beta, kappa)
    out = []
    for i in range(len(ys)-1):
        if v[i]*v[i+1] < 0:
            out.append(brentq(lambda y: Lcal(c, y, beta, kappa), ys[i], ys[i+1], xtol=1e-14))
    return out

def divergent(y, beta, kappa):
    X = xi_coeffs(kappa, y, beta)
    for L in LS:
        if PL_feasible(X, L, 0.0):
            return L
    return None

if __name__ == '__main__':
    KAPPA = float(sys.argv[1]); B0, B1, NB = float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]); OUT = sys.argv[5]
    res = []
    for beta in np.linspace(B0, B1, NB):
        y0, c0 = tangency(beta, KAPPA)
        if y0 is None: continue
        t4 = tongue_y(4, beta, KAPPA); t5 = tongue_y(5, beta, KAPPA)
        # bracket: just above the tangency (sigma>0) and the first tongue edge above it (in D)
        lo = y0+1e-9
        cands = [t for t in t4+t5 if t > y0]
        if not cands:
            res.append(dict(beta=beta, y0=y0, c0=c0, t4=t4, t5=t5, yb=None)); continue
        hi = min(cands)+1e-9
        while hi-lo > 1e-8:
            m = 0.5*(lo+hi)
            if divergent(m, beta, KAPPA): hi = m
            else: lo = m
        X = xi_coeffs(KAPPA, hi, beta)
        best = None
        for L in LS:
            if not PL_feasible(X, L, 1e-6): continue
            sL = sigma_L(X, L, lo=-0.05, hi=1e-6, tol=1e-11)
            if best is None or sL < best[0]: best = (sL, L)
        ok, (w, nu, t) = PL_feasible(X, best[1], best[0]+1e-9, ret=True)
        sup = [(float(w[i]/(2*pi)), float(nu[i])) for i in range(len(w)) if nu[i] > 1e-6]
        res.append(dict(beta=beta, y0=y0, c0=c0, t4=t4, t5=t5, yb=hi, L=best[1], sL=best[0], support=sup))
        print(beta, y0, hi, best, max(sup, key=lambda p: p[1]), flush=True)
    json.dump(res, open(OUT, 'w'))
