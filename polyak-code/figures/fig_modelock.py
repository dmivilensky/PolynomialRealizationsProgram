"""Figure 12: the exact two-lag point q* of 3/13 in I_4 (Theorem 10.17):
(a) the curve Theta with the two atoms of the threshold extremal, (b) the optimal symbol
T = lambda_1 Lambda_1 + lambda_{-4} Lambda_{-4}, (c) quantitative locking: sigma_L - sigma for L <= 130 against the squared
distance from Omega_L to the support, with the lower bound of Theorem 10.10(b) and the line c_* d^2."""
import numpy as np, sys
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbstyle import *
from hbtools import *
from math import pi
setup()
kap, aL, bet = 83.534303580146830096, 2.2189087648701528865, 0.62276758054145154889
X = xi_coeffs(kap, aL, bet)
th = lambda w: theta_of(X, w)
def Lam(n, w):
    t = th(w); return np.cos(t)-np.cos(n*w-t)
u1, u2 = 2*pi*3/13, 2*pi*2/13
l1 = -Lam(-4, u1); l4 = Lam(1, u1); s = l1+l4; l1, l4 = l1/s, l4/s
T = lambda w: l1*Lam(1, w)+l4*Lam(-4, w)
w1 = -Lam(1, u2); w2 = Lam(1, u1); ws = w1+w2; wa, wc = w1/ws, w2/ws   # weights at u1 (anchor), u2
fig, axs = plt.subplots(1, 3, figsize=(5.4, 1.75), gridspec_kw=dict(wspace=0.5))
# (a) the curve and the grid
ax = axs[0]
w = np.linspace(0.12*2*pi, 0.29*2*pi, 800)
ax.plot(w/(2*pi), th(w), color=C['cblue'], lw=1.1, zorder=3)
ax.plot(w/(2*pi), w/2, '--', color=C['ink'], lw=0.6, zorder=2)
dip = th(w) < w/2
ax.fill_between(w/(2*pi), th(w), w/2, where=dip, color=C['lred'], lw=0, zorder=1)
g = 2*pi*np.arange(1, 7)/13
ax.plot(g/(2*pi), th(g), 'o', ms=2.2, color=C['dgrey'], zorder=4)
ax.plot([u2/(2*pi)], [th(u2)], 'o', ms=9*np.sqrt(wc), color=C['violet'], zorder=5)
ax.plot([u1/(2*pi)], [th(u1)], 'o', ms=9*np.sqrt(wa), color=C['red'], zorder=5)
for K in (4, 5):
    ax.plot([1/K], [pi/K], 'o', ms=2.6, color=C['black'], zorder=5)
    ax.text(1/K+0.002, pi/K-0.035, r'$1/%d$' % K, fontsize=6.5)
ax.text(u1/(2*pi)+0.003, th(u1)-0.05, r'$3/13$', fontsize=6.5, color=C['red'])
ax.text(u2/(2*pi)+0.004, th(u2)+0.04, r'$2/13$', fontsize=6.5, color=C['violet'], ha='left')
ax.set_xlim(0.12, 0.29); ax.set_ylim(0.45, 1.25)
ax.set_xlabel(r'$\omega/2\pi$'); ax.set_ylabel(r'$\Theta(\omega)$')
ax.set_title(r'(a) the comb on $\Omega_{13}$')
# (b) the two-lag symbol
ax = axs[1]
w = np.linspace(1e-4, pi, 4000)
ax.plot(w/(2*pi), T(w), color=C['cgreen'], lw=1.0)
for x in 2*pi*np.arange(1,7)/13: ax.axvline(x/(2*pi), color=C['grey'], lw=0.5, zorder=0)
ax.axhline(0, color=C['ink'], lw=0.4)
ax.plot([u2/(2*pi)], [0], 'o', ms=9*np.sqrt(wc), color=C['violet'], zorder=5)
ax.plot([u1/(2*pi)], [0], 'o', ms=9*np.sqrt(wa), color=C['red'], zorder=5)
ax.set_xlim(0, 0.32); ax.set_ylim(-0.16, 0.02)
ax.set_xlabel(r'$\omega/2\pi$'); ax.set_ylabel(r'$T(\omega)$')
ax.set_title(r'(b) the optimal symbol')
# (c) quantitative locking
ax = axs[2]
S = np.array([u2, u1])
Pf = lambda w: l1*(1-np.cos(w))+l4*(1-np.cos(4*w))
def d2(w, h=1e-5): return (T(w+h)-2*T(w)+T(w-h))/h**2
cst = min(abs(d2(x))/(2*np.sin(th(x))*Pf(x)) for x in S)
Rs = lambda w: -T(w)/(np.sin(th(w))*Pf(w))
xs, ys, bs = [], [], []
for L in range(3, 131):
    if L % 13 == 0: continue
    sL = sigma_L(X, L, lo=-1.0, hi=2.0, tol=1e-11)
    gL = 2*pi*np.arange(1, L//2+1)/L
    dd = np.min(np.abs(gL[:, None]-S[None, :]))
    xs.append(dd**2); ys.append(sL); bs.append(np.min(Rs(gL[gL < pi-1e-9])))
xs, ys, bs = np.array(xs), np.array(ys), np.array(bs)
ax.loglog(xs, ys, 'o', ms=1.8, color=C['violet'], zorder=4)
ax.loglog(xs, bs, 'o', ms=2.4, mfc='none', mec=C['orange'], mew=0.5, zorder=3)
xx = np.logspace(np.log10(xs.min())-0.2, np.log10(xs.max())+0.2, 50)
ax.loglog(xx, cst*xx, '-', color=C['red'], lw=0.9, zorder=3)
ax.set_xlabel(r'$d(\Omega_L,S)^2$'); ax.set_ylabel(r'$\sigma_L-\sigma$')
ax.set_title(r'(c) locking, $L\leq130$')
ax.text(0.05, 0.86, r'$c_*d^2$', transform=ax.transAxes, color=C['red'], fontsize=7)
save_figure(fig, 'fig_modelock')
print('bound ok', np.all(ys >= bs-1e-8), np.min(ys-bs)); print('cstar', cst, 'weights', wa, wc, 'lam', l1, l4, 'min ratio', np.min(ys/(cst*xs)))
