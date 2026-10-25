"""Exact reusable algebra, refactored from the supplied Part I computations.
See PROVENANCE.json for original source hashes.
"""
"""Common exact objects for hb_an/struct (sympy, exact rationals only).
X = e^t = rho, Y = e^v (v = t - ln q, i.e. q = X/Y), c = cos w.
a_m = g (ch mt - cos mw), b_m = 2 sh v sin w sin mw, g = sin^2 w - sh^2 v.
Normalized constraint functionals (C-free parts), r_m = sh t / sh mt:
  lower m (L_m):  r_m (a_m - b_m)   [C-coefficient + sh t]
  upper m (U_m):  r_m (a_m + b_m)   [C-coefficient - sh t]
"""
import sympy as sp
X, Y, c, W, q = sp.symbols('X Y c W q')
shX = lambda m: (X ** m - X ** (-m)) / 2
chX = lambda m: (X ** m + X ** (-m)) / 2
shv = (Y - 1 / Y) / 2
g = 1 - c ** 2 - shv ** 2

def Tch(m):
    return sp.chebyshevt(m, c)

def Uch(m):
    return sp.chebyshevu(m, c)

def a(m):
    return g * (chX(m) - Tch(m))

def b(m):
    return 2 * shv * (1 - c ** 2) * Uch(m - 1)

def r(m):
    return shX(1) / shX(m)

def Lfun(m):
    return sp.together(r(m) * (a(m) - b(m)))

def Ufun(m):
    return sp.together(r(m) * (a(m) + b(m)))
S = (1 + X ** 2) * (Y ** 2 - 2 * Y - 1) + 2 * X * Y
F = lambda rho, qq: rho ** 2 * (rho ** 2 + 1) - 2 * qq * rho * (rho ** 2 - rho + 1) - qq ** 2 * (rho ** 2 + 1)
H = lambda rho, qq: (rho - qq) ** 2 * (rho ** 2 + 1) - 2 * qq * (qq - (1 - qq) * rho ** 2)

def numer(e):
    return sp.numer(sp.factor(sp.together(e)))
