"""Figure 7: the gap I_4 in the coordinates (a, r1, r2) of Proposition 8.12,
classified by the periodic programs of period at most 70 at the shift 0, at a = 1.1 a_0, 200, 2000
(data from data_gapchart.py)."""
import json, numpy as np, sys
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbstyle import *
from math import pi, cos, sin
from fractions import Fraction
setup()
K = 4; lo, hi = 1/5, 1/4
dc = json.load(open('gapchart_l1.1.json')); dd = json.load(open('gapchart_200.json')); df = json.load(open('gapchart_2000.json'))
panels = [(dc['l1.1'], r'(a) $a=1.1\,a_0$', None, 36), (dd['200'], r'(b) $a=200$', 200.0, 36), (df['2000'], r'(c) $a=2000$', 2000.0, 40)]
fig, axs = plt.subplots(1, 3, figsize=(5.3, 1.75), gridspec_kw=dict(wspace=0.12))
for ax, (data, title, afix, N) in zip(axs, panels):
    h = (hi-lo)/N
    tri = plt.Polygon([(lo, lo), (lo, hi), (hi, hi)], closed=True, fc=C['green'], ec='none', zorder=1)
    ax.add_patch(tri)
    for p1, p2, st, extra in data:
        if st == 1:
            ax.add_patch(plt.Rectangle((p1-h/2, p2-h/2), h, h, fc=C['red'], ec='none', zorder=2))
        elif st == -2:
            ax.add_patch(plt.Rectangle((p1-h/2, p2-h/2), h, h, fc=C['grey'], ec='none', zorder=2))
    # clip the cells along the diagonal
    ax.add_patch(plt.Polygon([(lo-0.01, lo-0.01), (hi+0.01, hi+0.01), (hi+0.01, lo-0.01)], closed=True, fc='white', ec='none', zorder=3))
    ax.plot([lo, hi], [lo, hi], color=C['ink'], lw=0.9, zorder=4)
    ax.plot([lo, lo], [lo, hi], color=C['lblue'], lw=2.2, zorder=4, solid_capstyle='butt')
    ax.plot([lo, hi], [hi, hi], color=C['blue'], lw=2.2, zorder=4, solid_capstyle='butt')
    if afix is not None:
        for j, k in [(2, 9), (3, 13), (3, 14), (4, 17), (5, 21), (5, 23)]:
            c = cos(2*pi*j/k); hh = sin(2*pi*j/k)/np.tan(pi/k); num = hh-1-c
            r = j/k
            ps = np.linspace(lo, r, 300); qs = []
            for p1 in ps:
                r2 = cos(2*pi*p1)
                # need (c-r1)(r2-c) >= num/a  ->  c-r1 >= num/(a(r2-c))
                if r2-c <= 0: qs.append(np.nan); continue
                r1 = c-num/(afix*(r2-c))
                qs.append(np.arccos(r1)/(2*pi) if -1 < r1 < 1 else np.nan)
            qs = np.array(qs); ok = (qs >= r) & (qs <= hi)
            ax.plot(ps[ok], qs[ok], color=C['violet'], lw=0.5, alpha=0.85, zorder=5)
            ax.plot([r], [r], 'o', ms=1.6, color=C['violet'], zorder=5)
        if afix < 1000:
            ax.text(0.2062, 0.2415, r'$2/9$', fontsize=7, color='white', zorder=6)
        else:
            for (x, y, t) in [(0.2075, 0.2415, r'$2/9$'), (0.2155, 0.2438, r'$3/13$'), (0.2025, 0.226, r'$3/14$'), (0.2215, 0.2462, r'$4/17$')]:
                ax.text(x, y, t, fontsize=6.3, color='white', zorder=6)
    ax.set_xlim(lo-0.0015, hi+0.0015); ax.set_ylim(lo-0.0015, hi+0.0015); ax.set_aspect('equal')
    ax.set_xticks([0.2, 0.25]); ax.set_xticklabels([r'$1/5$', r'$1/4$'])
    ax.set_yticks([0.2, 0.25]); ax.set_yticklabels([r'$1/5$', r'$1/4$'] if ax is axs[0] else [])
    ax.set_xlabel(r'$\varphi_1$', labelpad=-4)
    if ax is axs[0]: ax.set_ylabel(r'$\varphi_2$', labelpad=-6)
    ax.set_title(title)
    for s in ax.spines.values(): s.set_visible(False)
axs[0].annotate('junction', (lo, hi), (lo+0.012, hi-0.003), fontsize=6.5, arrowprops=dict(arrowstyle='-', lw=0.4, color=C['ink']), zorder=7)
axs[0].text(0.229, 0.2235, r'$\partial\Omega_1$', fontsize=7, rotation=45, zorder=7)
save_figure(fig, 'fig_gapchart')
print('ok')
