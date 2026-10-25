"""Tangency with the boundary of Omega_1 and the tongue edges at fixed (beta, kappa), for the staircase figure."""
import numpy as np
from math import pi, cos
from scipy.optimize import brentq
def Lcoef(y, beta, kappa):
    x = y/kappa
    return 4*beta, 2*(y-1-2*beta-beta**2+beta*x), (2-2*x+x*y+2*beta**2-2*beta*y)
def tangency(beta, kappa):
    def disc(y):
        a, b, c = Lcoef(y, beta, kappa); return b*b-4*a*c
    ys = np.linspace(0.3, 2*(1+beta)-1e-9, 4000)
    v = [disc(y) for y in ys]
    for i in range(len(ys)-1):
        if v[i] < 0 <= v[i+1] or v[i] >= 0 > v[i+1]:
            y0 = brentq(disc, ys[i], ys[i+1], xtol=1e-15)
            a, b, c = Lcoef(y0, beta, kappa); c0 = -b/(2*a)
            if -1 < c0 < 1: return y0, c0
    return None, None
def tongue_y(K, beta, kappa):
    c = cos(2*pi/K)
    f = lambda y: (lambda a, b, cc: a*c*c+b*c+cc)(*Lcoef(y, beta, kappa))
    ys = np.linspace(0.3, 2*(1+beta)-1e-9, 4000); v = [f(y) for y in ys]
    return [brentq(f, ys[i], ys[i+1], xtol=1e-15) for i in range(len(ys)-1) if v[i]*v[i+1] < 0]
