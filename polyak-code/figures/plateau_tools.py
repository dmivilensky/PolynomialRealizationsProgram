"""Edge of the tongue of j/k in the coordinates (a, D) (Section 11)."""
import numpy as np
from math import pi, cos, sin, tan, floor
from numpy.polynomial import chebyshev as Ch

class Fraction_edge:
    def __init__(self, j, k, K):
        self.j, self.k, self.K = j, k, K
        self.w0 = 2*pi*j/k; self.c0 = cos(self.w0); self.s0 = sin(self.w0)
        self.cp = pi/k; self.h0 = self.s0/tan(self.cp)
        self.b = pow(j, -1, k)
        self.C0 = self.h0-1-self.c0
        self.cK = cos(2*pi/K); self.cK1 = cos(2*pi/(K+1))
    def aE(self, D):
        h0, c0, C0 = self.h0, self.c0, self.C0
        t = [(h0+(1+D)*(1-c0))/(1-c0)**2, (h0-(1+D)*(1+c0))/(1+c0)**2,
             (C0+D*(self.cK-c0))/(self.cK-c0)**2, (C0+D*(self.cK1-c0))/(self.cK1-c0)**2]
        return max(t)
    def nbar(self, D):
        cp = self.cp
        return 2*sin(cp)**2*(1+D+cos(self.w0)/sin(self.w0)/tan(cp))
    def edge_lags(self, D):
        nb = self.nbar(D); k, b = self.k, self.b
        n1 = b+k*floor((nb-b)/k); th = (nb-n1)/k
        return n1, n1+k, th
    def a2(self, D):
        cp, s0, c0, k = self.cp, self.s0, self.c0, self.k
        n1, n2, th = self.edge_lags(D)
        Y = 1+D+cos(self.w0)/sin(self.w0)/tan(cp)
        return (1/tan(cp)*(1+c0**2)/(2*s0**3)+(1+D)*c0/(2*s0**2)
                - sin(cp)*cos(cp)*Y**2/s0+cos(cp)*k**2*th*(1-th)/(4*s0*sin(cp)**3))
    def Psi(self, lam, c):
        """Psi_lambda(c) for a dict lam {n: weight}; c an array in (-1,1)."""
        w = np.arccos(c)
        P = sum(l*(1-np.cos(n*w)) for n, l in lam.items())
        Q = sum(l*np.sin(n*w) for n, l in lam.items())
        return np.sin(w)*Q/P
    def R(self, lam, D, c):
        return (self.h0+(1+D)*(c-self.c0)-self.Psi(lam, c))/(c-self.c0)**2
    def maxR_edge(self, D, n=40001):
        n1, n2, th = self.edge_lags(D)
        lam = {n1: 1-th, n2: th}
        c = np.cos(np.linspace(1e-6, pi-1e-6, n))
        c = c[np.abs(c-self.c0) > 2e-3]
        v = self.R(lam, D, c)
        return max(float(np.max(v)), self.a2(D))

from scipy.optimize import linprog

def Xi_aD(F, a, D, c):
    return F.h0+(1+D)*(c-F.c0)-a*(c-F.c0)**2

def cert_margin(F, a, D, M=6, nw=3000):
    """Largest margin t of an admissible symbol with lags in L cap [-M k, M k] certifying q(a,D):
    sum_n lam_n G_n(c) <= -t on a grid, T''(omega_0) normalized <= -t (an LP)."""
    k, b, c0 = F.k, F.b, F.c0
    lags = [n for n in range(-M*k, M*k+1) if n != 0 and (n-b) % k == 0 or (n != 0 and n % k == 0)]
    lags = sorted(set(lags))
    w = np.linspace(1e-4, pi, nw)
    c = np.cos(w)
    keep = np.abs(c-c0) > 1e-3
    w, c = w[keep], c[keep]
    Xi = Xi_aD(F, a, D, c)
    nb = F.nbar(D)
    cp = F.cp; sp = sin(cp)
    s0 = F.s0
    Y = 1+D+cos(F.w0)/sin(F.w0)/tan(cp)
    X = F.h0*(1+c0**2)+(1+D)*s0**2*c0
    th2 = sp**2*(2*a*s0-X/s0**3)+2/tan(cp)*sp**4*Y**2
    rows = []; slope = []; sec = []
    for n in lags:
        g = Xi*(1-np.cos(n*w))-np.sin(w)*np.sin(n*w)
        rows.append(g/((1-c+1e-300)*(c-c0)**2))
        pos1 = (n-b) % k == 0
        slope.append((n-nb) if pos1 else -n)
        sec.append(cos(cp)*n*(n-nb)-(2*sp*th2 if pos1 else 0.0))
    G = np.array(rows).T            # (grid, lags)
    nl = len(lags)
    scaleG = np.maximum(np.abs(G).max(axis=1), 1e-12)
    Aub = np.vstack([G/scaleG[:, None], np.array(sec)[None, :]/max(1.0, np.abs(sec).max())])
    Aub = np.hstack([Aub, np.ones((Aub.shape[0], 1))])     # rows.lam + t <= 0
    Aeq = np.vstack([np.hstack([np.ones(nl), [0]]), np.hstack([np.array(slope, float), [0]])])
    beq = [1.0, 0.0]
    cobj = np.zeros(nl+1); cobj[-1] = -1
    res = linprog(cobj, A_ub=Aub, b_ub=np.zeros(Aub.shape[0]), A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)]*nl+[(None, 1.0)], method='highs')
    if res.status != 0: return -np.inf
    return -res.fun

def aF_est(F, D, lo, hi, M=6, tol=0.05):
    if cert_margin(F, hi, D, M) <= 0: return np.nan
    while hi-lo > tol:
        m = 0.5*(lo+hi)
        if cert_margin(F, m, D, M) > 0: hi = m
        else: lo = m
    return hi
