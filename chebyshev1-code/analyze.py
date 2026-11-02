"""Summaries of the measurements -> results/summary.json.

gossip_scan : mean squared error after N = 32 steps (95% normal intervals) and the excess,
              per graph, method and failure probability p
gossip(_gd) : the excess at three small p, normalized by sigma^2 = p/(1-p) and extrapolated
              to p -> 0 by weighted least squares in sigma^2 (y = Gamma + c sigma^2);
              ratios to the semi-iterative method with paired-bootstrap 95% intervals
              (common random numbers make run i comparable across methods)
energy      : |e_N| / r_0 over the r_0 grid; |e_N - p_N e_0| / r_0^2 at small r_0,
              extrapolated to r_0 -> 0 and compared with |Z(v)|
"""
import json, os
import numpy as np
from collections import defaultdict

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
RNG = np.random.default_rng(1)


def load(kind):
    f = os.path.join(OUT, f'raw_{kind}.npy')
    return list(np.load(f, allow_pickle=True)) if os.path.exists(f) else []


def wls(x, y, se):
    """Weighted least squares y = a + c x; returns a and its standard error."""
    W = 1.0 / se ** 2
    A = np.stack([np.ones_like(x), x], 1)
    C = np.linalg.inv(A.T @ (A * W[:, None]))
    a = C @ (A.T @ (W * y))
    return a[0], np.sqrt(C[0, 0])


def fit(levels_vals, idx=None):
    xs, ys, ses = [], [], []
    for p, v in sorted(levels_vals.items()):
        if idx is not None:
            v = v[idx[p]]
        s2 = p / (1 - p)
        xs.append(s2); ys.append(v.mean() / s2); ses.append(v.std(ddof=1) / np.sqrt(len(v)) / s2)
    return wls(*map(np.array, (xs, ys, ses)))


def gossip_fits(S, P, B=1000):
    D = defaultdict(lambda: defaultdict(dict))
    for kind in ('gossip', 'gossip_gd'):
        for spec, vals in load(kind):
            D[(kind, spec['inst'], spec['N'])][spec['method']][spec['level']] = np.asarray(vals, float)
    for (kind, inst, N), byM in sorted(D.items()):
        pred = P['gossip'][inst]['fit'][str(N)]
        fits = {m: fit(lv) for m, lv in byM.items()}
        M = len(next(iter(byM['pref'].values())))
        boots = defaultdict(list)
        for _ in range(B):
            idx = {p: RNG.integers(0, M, M) for p in byM['pref']}
            g = {m: fit(lv, idx)[0] for m, lv in byM.items()}
            for m in g:
                if m != 'pref':
                    boots[m].append(g[m] / g['pref'])
        e = {}
        for m, (a, se) in fits.items():
            e[m] = {'fit': a, 'se': se, 'pred': pred[m]}
            if m != 'pref':
                lo, hi = np.percentile(boots[m], [2.5, 97.5])
                e[m].update(ratio=a / fits['pref'][0], ratio_lo=lo, ratio_hi=hi,
                            ratio_pred=pred[m] / pred['pref'])
        S['gossip_fit'].setdefault(f'{kind}|{inst}', {})[N] = e


def gossip_scan(S, P):
    for spec, vals in load('gossip_scan'):
        full, exc = vals
        ok = np.isfinite(full)
        n = ok.sum()
        m, sd = full[ok].mean(), full[ok].std(ddof=1)
        pr = P['gossip'][spec['inst']]['scan'][spec['method']]
        s2 = spec['level'] / (1 - spec['level'])
        S['gossip_scan'].setdefault(spec['inst'], {}).setdefault(spec['method'], []).append({
            'p': spec['level'], 'mse': m, 'lo': m - 1.96 * sd / np.sqrt(n), 'hi': m + 1.96 * sd / np.sqrt(n),
            'excess': exc[ok].mean(), 'pred_mse': pr['det'] + s2 * pr['Gamma'], 'det': pr['det'],
            'finite': int(n), 'runs': len(full)})
    for inst in S['gossip_scan']:
        for m in S['gossip_scan'][inst]:
            S['gossip_scan'][inst][m].sort(key=lambda r: r['p'])


def energy(S, P):
    for spec, vals in load('energy'):
        r0 = np.array(spec['level']); err, dev = vals[:, 0], vals[:, 1]
        key = f"{spec['inst']}|{spec['N']}"
        if spec.get('fit'):
            y = dev / r0 ** 2
            a, _ = wls(r0, y, np.full_like(y, 1e-3 * y.mean()))
            S['energy_coef'].setdefault(spec['inst'], {}).setdefault(spec['N'], {})[spec['method']] = {
                'fit': a, 'pred': P['energy']['coef'][spec['inst']][str(spec['N'])][spec['method']]}
        else:
            S['energy_scan'].setdefault(spec['inst'], {})[spec['method']] = {
                'r0': r0.tolist(), 'rel_err': (err / r0).tolist(), 'dev_r2': (dev / r0 ** 2).tolist()}


if __name__ == '__main__':
    with open(os.path.join(OUT, 'pred.json')) as f:
        P = json.load(f)
    S = {'gossip_fit': {}, 'gossip_scan': {}, 'energy_coef': {}, 'energy_scan': {}}
    energy(S, P)
    gossip_scan(S, P)
    gossip_fits(S, P)
    with open(os.path.join(OUT, 'summary.json'), 'w') as f:
        json.dump(S, f, indent=1, default=float)
    print('summary written')
