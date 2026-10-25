"""Figure 14: the edge criterion F''(omega_*) at the junction tunings q_x(a) of the gaps I_3,...,I_6
(Proposition 12.4) and the thresholds of the fan pairs at q_x(4), q_x(8) of I_4 (Theorem 11.6)."""
import numpy as np, sys
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbstyle import *
from math import pi, cos, sin
from scipy.optimize import linprog
setup()
def junction(K, a):
    m = K+1; t1 = cos(2*pi/m); t2 = cos(2*pi/K)
    return (1-a*t1*t2, 1+a*(t1+t2), -a), t1, t2
def Fpp(K, a):
    m = K+1; c = pi/m; t1 = cos(2*pi/m); t2 = cos(2*pi/K)
    g = a*(t1-t2)*sin(c)**2
    return g*cos(c)*(4*g-(K+3)+2*(1-t1)/(t1-t2)+t1/(1+t1)), g
def a0(K):
    t1 = cos(2*pi/(K+1)); t2 = cos(2*pi/K); return 2/((1-t1)*(1-t2))
def theta(X, w, s):
    h = (X[0]+X[1]*np.cos(w)+X[2]*np.cos(w)**2)/np.sin(w)+s
    return pi/2-np.arctan(h)
def pair_feasible(X, L, j, jc, s):
    w = np.array([2*pi*j/L, 2*pi*jc/L]); th = theta(X, w, s)
    n = np.arange(1, L)
    A = np.cos(th)[None, :]-np.cos(n[:, None]*w[None, :]-th[None, :])
    A = np.vstack([A, np.cos(th)[None, :]])
    res = linprog([0, 0, -1], A_ub=np.hstack([-A, np.ones((A.shape[0], 1))]), b_ub=np.zeros(A.shape[0]),
                  A_eq=[[1, 1, 0]], b_eq=[1], bounds=[(0, None), (0, None), (None, 1)], method='highs')
    return res.status == 0 and -res.fun >= -1e-13
def pair_threshold(X, L, j, jc, lo=-0.05, hi=0.05):
    for _ in range(60):
        m = 0.5*(lo+hi)
        if pair_feasible(X, L, j, jc, m): hi = m
        else: lo = m
    return hi
fig, axs = plt.subplots(1, 2, figsize=(5.2, 1.85), gridspec_kw=dict(wspace=0.38))
ax = axs[0]
cols = {3: C['cgreen'], 4: C['red'], 5: C['violet'], 6: C['orange']}
for K in (3, 4, 5, 6):
    A0 = a0(K); aa = np.linspace(A0*1.0001, A0*3.0, 400)
    v = np.array([Fpp(K, a)[0] for a in aa])
    ax.plot(aa/A0, v, color=cols[K], lw=1.0, label=r'$K=%d$' % K)
    zero = aa[np.argmin(np.abs(v[10:]))+10]
ax.axhline(0, color=C['ink'], lw=0.5)
ax.set_xlim(1, 3); ax.set_ylim(-1.0, 1.2)
ax.set_xlabel(r'$a/a_0$ at the junction'); ax.set_ylabel(r'$F_q^{\prime\prime}(2\pi/(K+1))$')
ax.legend(frameon=False, loc='upper left', handlelength=1.2, borderaxespad=0.2)
ax.set_title(r'(a) the corners of the gaps')
ax = axs[1]
K = 4; m = 5; c = pi/m
for a, col in [(4.0, C['red']), (8.0, C['cblue'])]:
    X, t1, t2 = junction(K, a)
    F, g = Fpp(K, a); pred = K*F/(2*sin(c)**3)
    for vs, mk in [(-1, 'o'), (1, 's')]:
        Ls = [L for L in range(16, 330) if L % m == vs % m]
        dd, yy = [], []
        for L in Ls:
            j = (L-vs)//m; jc = j+vs
            sp = pair_threshold(X, L, j, jc)
            dl = 2*pi/(m*L); dd.append(dl); yy.append(sp/dl**2)
        ax.plot(dd, yy, mk, ms=1.8, color=col, mfc=col if vs < 0 else 'none', mew=0.5)
    ax.axhline(pred, color=col, lw=0.7, ls='--')
    ax.text(0.081, pred+0.35, r'$a=%g$' % a, color=col, fontsize=7, ha='right')
ax.axhline(0, color=C['ink'], lw=0.4)
ax.set_xlim(0, 0.082)
ax.set_xlabel(r'$\delta=2\pi/(5L)$'); ax.set_ylabel(r'$(s^{\rm pair}_L-s_*)/\delta^2$')
ax.set_title(r'(b) fan pairs at $q_\times(4)$ and $q_\times(8)$')
ax.set_ylim(-4, 13)
save_figure(fig, 'fig_edges')
for K in (3,4,5,6):
    A0=a0(K); aa=np.linspace(A0*1.0001,A0*5,20000); v=np.array([Fpp(K,a)[0] for a in aa]); print(K, A0, aa[np.where(v>0)[0][0]], aa[np.where(v>0)[0][0]]/A0)
