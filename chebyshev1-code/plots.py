"""Figure 1 of Section 9.  Usage: python3 plots.py  (reads results/*.json, writes ../fig_experiments.pdf)

Both panels show the error after one block of N gradient steps relative to the error of
the same block without Hessian variation, which is the same for all four methods (dotted
line at 1, all methods have the same polynomial p_N^*).  Lines: the prediction of
Corollary 8.1, computed before any simulation; markers: measurements.
(a) smooth energy, N = 64, x_0 = u* + r_0 v:   |e_N| / |p_N^*(H*) e_0|  against r_0;
    prediction |p_N^*(H*) v + r_0 Z(v)| / |p_N^*(H*) v|  (second order in r_0).
(b) gossip on the ring of cliques, N = 32:      E|e_N|^2 / E|p_N^*(L) e_0|^2  against the
    failure probability p; prediction 1 + (p/(1-p)) Gamma / E|p_N^*(L) e_0|^2 (first order in p).
"""
import json, os
import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator, LogLocator, NullFormatter

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
FIGDIR = os.path.dirname(HERE)

TEXTWIDTH = 338.0 / 72.27 - 0.03   # \textwidth of svjour3 smallextended (338pt), minus a margin
INK, INK2, GRID = '#1f1f1d', '#5c5b57', '#e6e5e0'
ORDER = ('pref', 'quarter', 'sine', 'gd')
COL = {'pref': '#5c5b57', 'quarter': '#2a78d6', 'sine': '#eb6834', 'gd': '#199e70'}
MARK = {'pref': 's', 'quarter': '^', 'sine': 'o', 'gd': 'D'}
NAME = {'pref': 'semi-iterative', 'quarter': r'Jacobi, $w_j\propto\sin^{1/2}\theta_j$',
        'sine': 'sine--Jacobi', 'gd': 'gradient descent'}
DOT = (0, (1.2, 1.6))

plt.rcParams.update({
    'text.usetex': True,
    'text.latex.preamble': r'\usepackage{lmodern}\usepackage{amsmath,amssymb}',
    'font.family': 'serif', 'font.size': 8, 'axes.labelsize': 8, 'xtick.labelsize': 7,
    'ytick.labelsize': 7, 'legend.fontsize': 7,
    'axes.edgecolor': INK2, 'axes.linewidth': 0.6, 'axes.labelcolor': INK,
    'xtick.color': INK2, 'ytick.color': INK2, 'xtick.major.width': 0.6, 'ytick.major.width': 0.6,
    'xtick.minor.width': 0.4, 'ytick.minor.width': 0.4, 'xtick.major.size': 2.5,
    'ytick.major.size': 2.5, 'xtick.minor.size': 1.5, 'ytick.minor.size': 1.5,
    'xtick.direction': 'out', 'ytick.direction': 'out',
    'axes.spines.top': False, 'axes.spines.right': False,
    'axes.grid': True, 'axes.grid.axis': 'both', 'grid.color': GRID, 'grid.linewidth': 0.5,
    'lines.linewidth': 1.0, 'errorbar.capsize': 0,
    'savefig.bbox': 'tight', 'savefig.pad_inches': 0.01,
})


def save(fig, name):
    """Adjust the width so that the tight bounding box is the text width (fonts at nominal size)."""
    for _ in range(10):
        bb = fig.get_tightbbox()
        fig.set_size_inches(fig.get_figwidth() + TEXTWIDTH - bb.width - 0.02, fig.get_figheight())
    fig.savefig(os.path.join(FIGDIR, name))
    plt.close(fig)


def load():
    with open(os.path.join(RES, 'pred.json')) as f:
        P = json.load(f)
    with open(os.path.join(RES, 'summary.json')) as f:
        S = json.load(f)
    return P, S


def baseline(ax):
    ax.axhline(1.0, color=INK2, lw=0.9, ls=DOT, zorder=1.5)


def letter(ax, s, x):
    ax.text(x, 1.02, rf'\textbf{{({s})}}', transform=ax.transAxes, fontsize=8.5, color=INK,
            va='bottom', ha='center')


def ratio_ticks(ax, ticks):
    ax.yaxis.set_major_locator(FixedLocator(ticks))
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f'{v:g}'))
    ax.yaxis.set_minor_locator(NullLocator())


def panel_energy(ax, P, S):
    pr = P['energy']['scan']['random']
    lin = pr['lin']
    sc = S['energy_scan']['random']
    r = np.logspace(-2, np.log10(30.0), 300)
    for m in ORDER:
        q = pr[m]
        pred = np.sqrt(lin ** 2 + 2 * r * q['lin_Z'] + r ** 2 * q['Z2']) / lin
        ax.plot(r, pred, color=COL[m], lw=1.0, zorder=2)
        r0 = np.array(sc[m]['r0']); y = np.array(sc[m]['rel_err']) / lin
        ok = np.isfinite(y)
        ax.plot(r0[ok], y[ok], MARK[m], ms=3.2, color=COL[m], mec='white', mew=0.5, zorder=3)
    baseline(ax)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlim(8e-3, 40); ax.set_ylim(0.75, 120)
    ratio_ticks(ax, [1, 2, 5, 10, 20, 50, 100])
    ax.xaxis.set_major_locator(LogLocator(base=10, numticks=6))
    ax.set_xlabel(r'initial distance $r_0=\|x_0-x^\star\|$')
    ax.set_ylabel(r'$\|e_N\|\,/\,\|p_N^\star(H_\star)e_0\|$')
    ax.yaxis.set_label_coords(-0.17, 0.5)
    letter(ax, 'a', -0.17)


def panel_gossip(ax, P, S, graph='ring of cliques'):
    sc = S['gossip_scan'][graph]
    pg = P['gossip'][graph]['scan']
    p = np.logspace(-5.2, -1.85, 300)
    for m in ORDER:
        det, Gam = pg[m]['det'], pg[m]['Gamma']
        ax.plot(p, 1 + p / (1 - p) * Gam / det, color=COL[m], lw=1.0, zorder=2)
        rows = sc[m]
        rows = [r for r in rows if r['p'] <= 1.1e-2]
        x = np.array([r['p'] for r in rows]); y = np.array([r['mse'] for r in rows]) / det
        lo = np.array([r['lo'] for r in rows]) / det; hi = np.array([r['hi'] for r in rows]) / det
        ax.errorbar(x, y, yerr=[np.maximum(y - lo, 0), hi - y], fmt=MARK[m], ms=3.2, color=COL[m],
                    mec='white', mew=0.5, elinewidth=0.6, zorder=3)
    baseline(ax)
    ax.set_xscale('log'); ax.set_yscale('log')
    ax.set_xlim(7e-6, 1.5e-2); ax.set_ylim(0.75, 600)
    ratio_ticks(ax, [1, 2, 5, 10, 20, 50, 100, 200, 500])
    ax.xaxis.set_major_locator(LogLocator(base=10, numticks=6))
    ax.set_xlabel(r'link-failure probability $p$')
    ax.set_ylabel(r'$\mathbb E\|e_N\|^2\,/\,\mathbb E\|p_N^\star(\mathcal L)e_0\|^2$')
    ax.yaxis.set_label_coords(-0.2, 0.5)
    letter(ax, 'b', -0.2)


def legend(fig):
    h = [Line2D([], [], color=COL[m], lw=1.0, marker=MARK[m], ms=3.2, mec='white', mew=0.5)
         for m in ORDER]
    h.append(Line2D([], [], color=INK2, lw=0.9, ls=DOT))
    lab = [NAME[m] for m in ORDER] + ['no variation']
    fig.legend(h, lab, loc='lower center', bbox_to_anchor=(0.5, 0.97), ncol=3,
               frameon=False, handlelength=1.8, handletextpad=0.4, columnspacing=1.2,
               borderaxespad=0.0)


def fig_experiments(P, S):
    fig, (a, b) = plt.subplots(1, 2, figsize=(TEXTWIDTH, 2.2), gridspec_kw={'wspace': 0.45})
    panel_energy(a, P, S)
    panel_gossip(b, P, S)
    legend(fig)
    save(fig, 'fig_experiments.pdf')


if __name__ == '__main__':
    P, S = load()
    fig_experiments(P, S)
    print('figure written to', FIGDIR)
