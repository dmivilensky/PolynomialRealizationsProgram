"""Figure 11: the boundary of the divergence set across the gap I_4 at kappa = 150, in the coordinate
alpha L - alpha_partial(beta), with the heaviest atom of the program with the least threshold
(data from data_staircase.py)."""
import json, numpy as np, sys
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbstyle import *
from fractions import Fraction
from math import pi, acos
from tongue_geom import tangency, tongue_y
import matplotlib.gridspec as gridspec
setup()
K = 150.0
d = json.load(open('st150a.json'))+json.load(open('st150b.json'))
bf = np.linspace(0.53, 0.69, 1601)
rows = []
for b in bf:
    y0, c0 = tangency(b, K)
    rows.append((acos(c0)/(2*pi), y0, tongue_y(4, b, K), tongue_y(5, b, K)))
rot_f = np.array([r[0] for r in rows])
def low(ts, y0):
    ts = [t for t in ts if t > y0-1e-12]
    return min(ts)-y0 if ts else np.inf
l4 = np.array([low(r[2], r[1]) for r in rows]); l5 = np.array([low(r[3], r[1]) for r in rows])
o = np.argsort(rot_f); rot_f, l4, l5 = rot_f[o], l4[o], l5[o]
rot = np.array([acos(r['c0'])/(2*pi) for r in d]); hb = np.array([r['yb']-r['y0'] for r in d])
anc = [Fraction(max(r['support'], key=lambda p: p[1])[0]).limit_denominator(400) for r in d]
o = np.argsort(rot); rot, hb, anc = rot[o], hb[o], [anc[i] for i in o]
segs = []; i = 0
while i < len(anc):
    j = i
    while j+1 < len(anc) and anc[j+1] == anc[i]: j += 1
    segs.append((i, j, anc[i])); i = j+1
# boundary of D in the gap, on the fine grid: B4 inside its range, tongue edge outside
edge = np.fmin(l4, l5)
bnd = edge.copy()
inr = (rot_f >= rot.min()) & (rot_f <= rot.max())
bnd[inr] = np.interp(rot_f[inr], rot, hb)
YMAX = 0.085
fig = plt.figure(figsize=(5.2, 3.2))
gs = gridspec.GridSpec(2, 2, figure=fig, height_ratios=[1, 0.9], width_ratios=[1, 1], hspace=0.50, wspace=0.3)
def gap_panel(ax, xl, yl, labels):
    ax.fill_between(rot_f, np.minimum(l4, yl[1]), yl[1], where=l4 < yl[1], color=C['blue'], lw=0, zorder=1)
    ax.fill_between(rot_f, np.minimum(l5, yl[1]), yl[1], where=l5 < yl[1], color=C['lblue'], lw=0, zorder=1)
    ax.fill_between(rot_f, 0, np.minimum(bnd, yl[1]), color=C['green'], lw=0, zorder=2)
    ax.fill_between(rot_f, np.minimum(bnd, yl[1]), np.minimum(edge, yl[1]), where=edge > bnd, color=C['lred'], lw=0, zorder=2)
    ax.plot(rot, hb, color=C['ink'], lw=0.5, zorder=3)
    for (i, j, a) in segs:
        if j > i and labels:
            ax.plot(rot[i:j+1], hb[i:j+1], color=C['red'], lw=2.2, solid_capstyle='butt', zorder=4)
    ax.set_xlim(*xl); ax.set_ylim(*yl)
ax = fig.add_subplot(gs[0, 0])
gap_panel(ax, (0.196, 0.254), (0, YMAX), False)
ax.add_patch(plt.Rectangle((0.2145, 0.035), 0.014, 0.022, fill=False, ec=C['ink'], lw=0.6, zorder=6))
ax.text(0.2515, 0.072, r'$4$', ha='center'); ax.text(0.1985, 0.072, r'$5$', ha='center')
ax.text(0.222, 0.012, r'$I_4$', ha='center', fontsize=8)
ax.set_xticks([0.2, 0.22, 0.24]); ax.set_xlabel(r'$\omega_*/2\pi$'); ax.set_ylabel(r'$\alpha L-\alpha_\partial(\beta)$')
ax.set_title(r'(a) the gap $I_4$ at $\kappa=150$')
ax = fig.add_subplot(gs[0, 1])
gap_panel(ax, (0.2145, 0.2285), (0.035, 0.057), True)
for frac, dx, dy in [(Fraction(3, 13), 0.0, 0.0016), (Fraction(2, 9), -0.0006, 0.0016), (Fraction(5, 21), 0.0006, 0.0030), (Fraction(5, 23), -0.0008, 0.0012), (Fraction(7, 29), 0.0008, 0.0012)]:
    idx = [k for k in range(len(anc)) if anc[k] == frac]
    m = idx[len(idx)//2]
    ax.text(rot[m]+dx, hb[m]+dy, r'$%d/%d$' % (frac.numerator, frac.denominator), ha='center', fontsize=6.8, zorder=7,
            bbox=dict(boxstyle='round,pad=0.12', fc='white', ec='none', alpha=0.85))
ax.text(0.2272, 0.0418, r'$1/4$', ha='right', fontsize=6.8, zorder=7, bbox=dict(boxstyle='round,pad=0.12', fc='white', ec='none', alpha=0.85))
ax.text(0.2163, 0.0360, r'$1/5$', ha='left', fontsize=6.8, zorder=7, bbox=dict(boxstyle='round,pad=0.12', fc='white', ec='none', alpha=0.85))
ax.text(0.2215, 0.0405, r'$\sigma>0$', ha='center', fontsize=7)
ax.text(0.2215, 0.0553, r'$\sigma<0$', ha='center', fontsize=7)
ax.set_xticks([0.216, 0.22, 0.224, 0.228]); ax.set_xlabel(r'$\omega_*/2\pi$')
ax.set_title(r'(b) the boundary $\mathcal{B}_4$, magnified')
ax = fig.add_subplot(gs[1, :])
ya = np.array([float(a) for a in anc])
ax.step(rot, ya, where='mid', color=C['ink'], lw=0.6, zorder=3)
for (i, j, a) in segs:
    if j > i:
        ax.plot([rot[i]-0.00004, rot[j]+0.00004], [ya[i], ya[i]], color=C['red'], lw=3.0, solid_capstyle='butt', zorder=4)
lab = {Fraction(1, 4): -0.006, Fraction(9, 37): 0.0045, Fraction(7, 29): 0.0012, Fraction(5, 21): 0.0012, Fraction(4, 17): 0.0012,
       Fraction(3, 13): 0.0012, Fraction(7, 31): 0.0012, Fraction(2, 9): 0.0012, Fraction(5, 23): 0.0012, Fraction(6, 29): 0.0012, Fraction(1, 5): 0.0012}
for frac, dy in lab.items():
    idx = [k for k in range(len(anc)) if anc[k] == frac]
    if idx:
        m = 0.5*(rot[idx[0]]+rot[idx[-1]])
        ax.text(m, float(frac)+dy, r'$%d/%d$' % (frac.numerator, frac.denominator), fontsize=6.3, ha='center', va='bottom')
ax.plot(rot, ya, 'o', ms=0.9, color=C['ink'], zorder=3)
ax.set_xlim(0.2155, 0.2275); ax.set_ylim(0.197, 0.254)
ax.set_xlabel(r'rotation number $\omega_*/2\pi$ of the tangency')
ax.set_ylabel(r'anchor $j/k$')
ax.set_title(r'(c) the anchors along $\mathcal{B}_4$')
save_figure(fig, 'fig_staircase')
print('ok')
