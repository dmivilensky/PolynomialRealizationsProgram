"""Figure 8: tongue functions kappa_{j/k} across the gap I_4 at fixed beta, their lower envelope,
the divergence boundary kappa_partial located by periodic programs, and the staircase of the
fractions attaining the envelope (Lemma 9.2, Theorem 11.11, Proposition 11.13)."""
import sys, json, numpy as np
from math import pi, cos, sin, tan, asin, sqrt
from fractions import Fraction
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbstyle import *
import matplotlib.gridspec as gridspec
setup()

def kappa_jk(j, k, y, b):
    c0 = cos(2*pi*j/k); s0 = sin(2*pi*j/k); h0 = s0/tan(pi/k)
    den = (1-c0)*(y*(1+b)-2*(1-2*b*c0+b*b))-h0*y*(1-b)
    return np.where(den > 0, 1+((y-(1+b)*(1-c0))**2+(1-b)**2*s0**2)/np.where(den > 0, den, 1), np.inf)

d = json.load(open('tongues_0.995.json'))
B = d['beta']
y = np.array(d['y']); kp = np.array([np.nan if v is None else v for v in d['kpartial']])
yf = np.array(d['yfine'])
om = np.array([np.nan if o is None else o[0] for o in d['omega']])
win = sorted({Fraction(j, k) for k in range(5, 61) for j in range(1, k) if Fraction(1, 5) < Fraction(j, k) < Fraction(1, 4)})
TT = {f: kappa_jk(f.numerator, f.denominator, yf, B) for f in win}
k4 = kappa_jk(1, 4, yf, B); k5 = kappa_jk(1, 5, yf, B)
allf = [Fraction(1, 5)]+win+[Fraction(1, 4)]
M = np.vstack([k5]+[TT[f] for f in win]+[k4])
env = M.min(axis=0); arg = M.argmin(axis=0)

fig = plt.figure(figsize=(5.2, 3.55))
gs = gridspec.GridSpec(2, 1, figure=fig, height_ratios=[1.25, 1.15], hspace=0.48)
ax = fig.add_subplot(gs[0])
top = 0.16
ax.fill_between(yf, np.minimum(k5-1, top), top, where=np.isfinite(k5), color=C['lblue'], lw=0, zorder=1)
ax.fill_between(yf, np.minimum(k4-1, top), top, where=np.isfinite(k4), color=C['blue'], lw=0, zorder=1)
ax.fill_between(yf, 1e-4, om-1, color=C['green'], lw=0, zorder=1)
for f in win:
    if f.denominator <= 30:
        ax.plot(yf, TT[f]-1, color=C['dgrey'], lw=0.35, zorder=2)
ok = np.isfinite(env)
ax.plot(yf[ok], env[ok]-1, color=C['violet'], lw=1.3, zorder=3)
ax.plot(yf, om-1, color=C['ink'], lw=0.6, ls='--', zorder=3)
yk = np.interp(y, yf, env)
sel = np.isfinite(yk) & np.isfinite(kp)
ax.plot(y[sel], kp[sel]-1, 'o', ms=1.5, color=C['black'], zorder=4)
labels = {}
for i in range(len(yf)):
    f = allf[arg[i]]
    if np.isfinite(env[i]) and Fraction(1, 5) < f < Fraction(1, 4):
        labels.setdefault(f, []).append(i)
for f, idx in labels.items():
    if len(idx) < 12: continue
    m = idx[int(np.argmin(env[idx]))]
    ax.text(yf[m], env[m]-1-0.0045, r'$%d/%d$' % (f.numerator, f.denominator), ha='center', va='top', fontsize=6.3, zorder=5,
            bbox=dict(boxstyle='round,pad=0.08', fc='white', ec='none', alpha=0.8))
ax.text(1.40, 0.135, r'$1/5$', fontsize=7); ax.text(2.006, 0.135, r'$1/4$', fontsize=7)
ax.text(1.70, 0.0085, r'$\Omega_1$', fontsize=7)
ax.set_xlim(1.38, yf[-1]); ax.set_ylim(0.005, top)
ax.set_xlabel(r'$\alpha L$'); ax.set_ylabel(r'$\kappa-1$')
ax.set_title(r'(a) the tongue functions across $I_4$ at $\beta=%.3f$' % B)

ax = fig.add_subplot(gs[1])
ys = np.linspace(1.37, 2.03, 6001)
cols = {0.99: C['orange'], 0.995: C['violet'], 0.999: C['cblue']}
win2 = sorted({Fraction(j, k) for k in range(5, 80) for j in range(1, k) if Fraction(1, 5) <= Fraction(j, k) <= Fraction(1, 4)})
for b, col in cols.items():
    MM = np.vstack([kappa_jk(f.numerator, f.denominator, ys, b) for f in win2])
    a = MM.argmin(axis=0); e = MM.min(axis=0)
    val = np.array([float(win2[i]) for i in a]); val[~np.isfinite(e)] = np.nan
    ax.step(ys, val, where='mid', color=col, lw=0.9, label=r'$\beta=%g$' % b)
ax.plot(ys, [asin(sqrt(v)/2)/pi for v in ys], color=C['ink'], lw=0.6, ls='--', label=r'$\arcsin(\sqrt{\alpha L}/2)/\pi$')
tk = [Fraction(1, 5), Fraction(4, 19), Fraction(3, 14), Fraction(2, 9), Fraction(3, 13), Fraction(4, 17), Fraction(1, 4)]
ax.set_yticks([float(f) for f in tk]); ax.set_yticklabels([r'$%d/%d$' % (f.numerator, f.denominator) for f in tk])
ax.grid(axis='y', color=C['grey'], lw=0.4)
ax.set_xlim(1.37, 2.03); ax.set_ylim(0.197, 0.253)
ax.set_xlabel(r'$\alpha L$'); ax.set_ylabel(r'$j/k$')
ax.legend(loc='upper left', frameon=False, fontsize=6.5)
ax.set_title(r'(b) the fraction attaining $\min_{j/k}\kappa_{j/k}$')
save_figure(fig, 'fig_tongues')
print('ok')
