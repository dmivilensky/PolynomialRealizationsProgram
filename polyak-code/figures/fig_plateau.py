"""Figure 13: the single-harmonic plateau of 2/9 in the gap I_4 (Section 11):
(a) the coordinates (D, a) of the edge of the tongue, (b) the image of the plateau in the (alpha L, beta) plane."""
import sys, json, numpy as np
from math import pi, sin
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbstyle import *
import matplotlib.gridspec as gridspec
from matplotlib.colors import LogNorm
setup()
d = json.load(open('plateau_2_9.json'))
R = d['rows']
D = np.array([r['D'] for r in R]); aE = np.array([r['aE'] for r in R]); a2 = np.array([r['a2'] for r in R])
aF = np.array([r['aF'] for r in R]); mR = np.array([r['maxR'] for r in R]); nb = np.array([r['nbar'] for r in R])
k, b = d['k'], 5
fig = plt.figure(figsize=(5.2, 2.1))
gs = gridspec.GridSpec(1, 2, figure=fig, width_ratios=[1.25, 1], wspace=0.32)
ax = fig.add_subplot(gs[0])
TOP = 330
low = np.maximum(aE, aF)
ax.fill_between(D, low, TOP, color=C['green'], lw=0, zorder=1)
ax.fill_between(D, aE, np.maximum(aE, a2), where=a2 > aE, color=C['lred'], lw=0, zorder=1)
ax.fill_between(D, 0, aE, color=C['grey'], lw=0, zorder=1)
ax.plot(D, aE, color=C['ink'], lw=0.8, zorder=3, label=r'$a_E$')
ax.plot(D, np.where(a2 > aE, a2, np.nan), color=C['red'], lw=0.9, ls='--', zorder=3, label=r'$a_2$')
ax.plot(D, np.minimum(mR, TOP+50), color=C['violet'], lw=0.8, ls=':', zorder=3, label=r'$\max R_{\lambda^{\rm e}}$')
ax.plot(D, aF, color=C['black'], lw=0.9, zorder=4, label=r'$a_F$')
for n in [-4, 5]:
    Dn = n/(2*sin(pi/k)**2)-1-np.cos(2*pi*2/k)/np.sin(2*pi*2/k)/np.tan(pi/k)
    if D.min() < Dn < D.max(): ax.axvline(Dn, color=C['dgrey'], lw=0.5, ls=':', zorder=2)
ax.text(-6, 250, r'$\Pi_{2/9}$', fontsize=8)
ax.text(-4.5, 101, r'$\mathrm{int}\,\mathcal{D}$', fontsize=6.5, color=C['red'])
ax.text(2, 50, r'outside $I_4$', fontsize=6.5)
ax.set_xlim(D.min(), D.max()); ax.set_ylim(40, TOP)
ax.set_xlabel(r'$D$'); ax.set_ylabel(r'$a$')
ax.legend(loc='upper left', frameon=True, fontsize=6, framealpha=0.9, edgecolor='none', ncol=2)
ax.set_title(r'(a) the edge of the tongue of $2/9$')
ax = fig.add_subplot(gs[1])
im = d['image']
x = np.array([p['aL'] for p in im]); yb = np.array([1-p['beta'] for p in im]); kk = np.array([p['kappa']-1 for p in im])
nD = len({p['D'] for p in im}); x, yb, kk = (v.reshape(nD, -1) for v in (x, yb, kk))
sc = ax.pcolormesh(x, yb, kk, cmap='viridis', norm=LogNorm(vmin=kk.min(), vmax=kk.max()), shading='gouraud', zorder=2, rasterized=True)
ax.axvline(4*sin(2*pi/9)**2, color=C['ink'], lw=0.5, ls='--', zorder=1)
ax.set_yscale('log')
ax.set_xlabel(r'$\alpha L$'); ax.set_ylabel(r'$1-\beta$')
cb = fig.colorbar(sc, ax=ax, pad=0.02, fraction=0.06); cb.set_label(r'$\kappa_\partial-1=\kappa_{2/9}-1$', fontsize=7)
cb.ax.tick_params(labelsize=6)
ax.set_title(r'(b) $\Pi_{2/9}$ in the $(\alpha L,\beta)$ plane')
save_figure(fig, 'fig_plateau')
print('ok')
