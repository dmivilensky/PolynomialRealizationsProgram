"""Numerical tools for the threshold problem used by the figure scripts: the quadratic Xi of a tuning,
the angle function, and the periodic programs P_L (linear programs over the grid Omega_L)."""
import numpy as np
from scipy.optimize import linprog
from math import pi, gcd

def xi_coeffs(kappa, aL, beta):
    y = aL; x = aL/kappa
    A = 1+beta-(x+y)/2; B = (y-x)/2
    den = 2*B*(1-beta)
    X0 = (B*B-(1-beta)**2-A*A)/den
    X1 = 2*A*(1+beta)/den
    X2 = -4*beta/den
    return X0, X1, X2

def h_of(X, w):
    c = np.cos(w); return (X[0]+X[1]*c+X[2]*c*c)/np.sin(w)

def theta_of(X, w, s=0.0):
    hv = h_of(X, w)+s
    return np.pi/2-np.arctan(hv)

def ell(hv, n, w):
    return hv*(1-np.cos(n*w))-np.sin(n*w)

def grid(L):
    j = np.arange(1, (L-1)//2+1)   # 0 < 2 pi j/L < pi
    return 2*pi*j/L, j

def PL_feasible(X, L, s=0.0, ret=False):
    """Feasibility of the L-periodic program at shift s (h-form, normalized nu)."""
    w, j = grid(L)
    if len(w) == 0: return (False, None) if ret else False
    hv = h_of(X, w)+s
    rows = []
    for r in range(1, L):
        rows.append(ell(hv, r, w))
    rows.append(hv)
    Aub = -np.array(rows)          # -(...) <= 0
    # maximize margin t: rows.nu >= t ; sum nu = 1
    n = len(w)
    c = np.zeros(n+1); c[-1] = -1
    Aub2 = np.hstack([Aub, np.ones((Aub.shape[0], 1))])
    res = linprog(c, A_ub=Aub2, b_ub=np.zeros(Aub.shape[0]),
                  A_eq=np.hstack([np.ones((1, n)), np.zeros((1, 1))]), b_eq=[1.0],
                  bounds=[(0, None)]*n+[(None, 1.0)], method='highs')
    ok = res.status == 0 and -res.fun >= -1e-12
    if ret: return ok, (w, res.x[:n] if res.status == 0 else None, -res.fun if res.status==0 else None)
    return ok

def sigma_L(X, L, lo=-5.0, hi=5.0, tol=1e-10):
    if not PL_feasible(X, L, hi):
        return np.inf
    if PL_feasible(X, L, lo):
        return -np.inf
    while hi-lo > tol:
        m = 0.5*(lo+hi)
        if PL_feasible(X, L, m): hi = m
        else: lo = m
    return hi

def dip(X, n=20001):
    w = np.linspace(1e-6, pi-1e-6, n)
    g = theta_of(X, w)-w/2
    idx = np.where(g < 0)[0]
    if len(idx) == 0: return None
    return w[idx[0]], w[idx[-1]]
