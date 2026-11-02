"""Run the experiments of Section 9: predictions (no simulation) and measurements.

    python3 run_all.py pred        # predictions only -> results/pred.json
    python3 run_all.py <kind>      # one kind: energy | gossip | gossip_gd | gossip_scan
    python3 run_all.py             # everything -> results/raw_<kind>.npy

Kinds:
  energy       exact runs on the smooth energy: the error after N = 64 steps over a grid of
               initial distances r_0 (Figure 1(a)), for the fixed random direction and 20 more,
               and the second-order coefficient |e_N - p_N e_0| / r_0^2 at small r_0 for
               N = 16, ..., 256 (compared with |Z(v)|)
  gossip_scan  mean squared error after N = 32 steps against the failure probability p,
               four graphs, four methods (Figure 1(b) shows the ring of cliques)
  gossip       excess at three small p for N = 8, 16, 24, 32 (pref, sine, quarter),
               extrapolated to p -> 0 and compared with Gamma
  gossip_gd    the same for gradient descent (lower p: it leaves the first-order range
               earlier), N = 8, 16, 32
"""
import json, os, sys, time, zlib
import numpy as np
from concurrent.futures import ProcessPoolExecutor
from common import METHODS, coefficients, Eig, chebyshev_eps
from predict import gossip_iso, Z_energy, linear_energy
from simulate import mc_gossip, run_energy
import models

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results')
os.makedirs(OUT, exist_ok=True)
SEED = 20261031
GOSSIP_FIT = [10 ** -4.5, 10 ** -4, 10 ** -3.5]
GOSSIP_GD_FIT = [10 ** -5, 10 ** -4.5, 10 ** -4]
GOSSIP_SCAN = [10 ** (-k / 2) for k in range(2, 11)]          # p = 10^-1, ..., 10^-5
ENERGY_N = 64
ENERGY_R0 = list(np.logspace(-2, np.log10(30.0), 16))
ENERGY_FIT_R0 = [1e-3, 3e-3, 1e-2]
N_DIRS = 20


def unit(v):
    return v / np.linalg.norm(v)


def gossip_instance(name):
    B, w, Lap, mu, L = models.gossip(name)
    return B, w, Lap, Eig(Lap), mu, L


def energy_instance():
    A, ustar, Hs = models.energy(63, 100.0)
    eig = Eig(Hs)
    rng = np.random.default_rng(SEED)
    slow = eig.U[:, 0] * np.sign(eig.U[:, 0].sum())
    dirs = {'slow mode': slow, 'random': unit(rng.standard_normal(63))}
    rng2 = np.random.default_rng(SEED + 1)
    for k in range(N_DIRS):
        dirs[f'random {k}'] = unit(rng2.standard_normal(63))
    return ustar, Hs, eig, eig.lam[0], eig.lam[-1], dirs


# ------------------------------------------------------------------ predictions
def predictions():
    P = {'gossip': {}, 'energy': {}}
    for name in models.GRAPHS:
        B, w, Lap, eig, mu, L = gossip_instance(name)
        g = {'kappa': L / mu, 'fit': {}, 'scan': {}}
        for N in (8, 16, 24, 32):
            g['fit'][N] = {m: gossip_iso(B, w, eig, N, mu, L, m)[1] for m in METHODS
                           if m != 'gd' or N & (N - 1) == 0}
        for m in METHODS:
            det, Gam = gossip_iso(B, w, eig, 32, mu, L, m)
            g['scan'][m] = {'det': det, 'Gamma': Gam}
        P['gossip'][name] = g
    ustar, Hs, eig, mu, L, dirs = energy_instance()
    E = {'kappa': L / mu, 'N': ENERGY_N, 'scan': {}, 'coef': {}}
    for dn, v in dirs.items():
        if dn == 'slow mode':
            continue
        lin = linear_energy(eig, ENERGY_N, mu, L, v, 'pref')
        E['scan'][dn] = {'lin': float(np.linalg.norm(lin))}
        for m in METHODS:
            Z = Z_energy(eig, ENERGY_N, mu, L, ustar, v, m)
            E['scan'][dn][m] = {'Z': float(np.linalg.norm(Z)), 'lin_Z': float(lin @ Z),
                                'Z2': float(Z @ Z)}
    for dn in ('slow mode', 'random'):
        E['coef'][dn] = {N: {m: float(np.linalg.norm(Z_energy(eig, N, mu, L, ustar, dirs[dn], m)))
                             for m in METHODS} for N in (16, 32, 64, 128, 256)}
    P['energy'] = E
    return P


# ------------------------------------------------------------------ measurement tasks
def task(spec):
    kind, t0 = spec['kind'], time.time()
    if kind.startswith('gossip'):
        B, w, Lap, eig, mu, L = gossip_instance(spec['inst'])
        coef = coefficients(spec['method'], spec['N'], mu, L)
        full, exc = mc_gossip(B, w, Lap, coef, spec['level'], spec['M'], spec['seed'])
        vals = np.stack([full, exc]) if kind == 'gossip_scan' else exc
    else:                                              # energy: deterministic
        ustar, Hs, eig, mu, L, dirs = energy_instance()
        coef = coefficients(spec['method'], spec['N'], mu, L)
        v = dirs[spec['inst']]
        rows = []
        for r in spec['level']:
            eN, dev = run_energy(Hs, ustar, coef, r * v)
            rows.append([np.linalg.norm(eN), np.linalg.norm(dev)])
        vals = np.array(rows)                          # (len(r0), 2): |e_N|, |e_N - p e_0|
    return spec, vals, time.time() - t0


def specs():
    S = []

    def add(kind, inst, N, methods, levels, M):
        for lev in levels:
            seed = zlib.crc32(repr((kind, inst, int(N), float(lev))).encode())  # common random numbers
            for m in methods:
                S.append(dict(kind=kind, inst=inst, N=int(N), method=m, level=lev, M=M, seed=seed))
    for name in models.GRAPHS:
        add('gossip_scan', name, 32, METHODS, GOSSIP_SCAN, 100000)
        for N in (8, 16, 24, 32):
            add('gossip', name, N, ('pref', 'sine', 'quarter'), GOSSIP_FIT, 100000)
        for N in (8, 16, 32):
            add('gossip_gd', name, N, ('pref', 'gd'), GOSSIP_GD_FIT, 300000)
    for m in METHODS:
        for dn in ['random'] + [f'random {k}' for k in range(N_DIRS)]:
            S.append(dict(kind='energy', inst=dn, N=ENERGY_N, method=m, level=ENERGY_R0, M=1, seed=0))
        for dn in ('slow mode', 'random'):
            for N in (16, 32, 64, 128, 256):
                S.append(dict(kind='energy', inst=dn, N=N, method=m, level=ENERGY_FIT_R0, M=1, seed=0,
                              fit=True))
    return S


if __name__ == '__main__':
    only = sys.argv[1] if len(sys.argv) > 1 else None
    if only in (None, 'pred'):
        with open(os.path.join(OUT, 'pred.json'), 'w') as f:
            json.dump(predictions(), f)
        print('predictions written', flush=True)
        if only == 'pred':
            sys.exit()
    kinds = [only] if only else ['energy', 'gossip_scan', 'gossip', 'gossip_gd']
    for kind in kinds:
        S = sorted((s for s in specs() if s['kind'] == kind), key=lambda s: -(s['N'] * s['M']))
        results = []
        with ProcessPoolExecutor(2) as ex:
            for i, (spec, vals, dt) in enumerate(ex.map(task, S)):
                results.append((spec, vals))
                print(f"[{i + 1}/{len(S)}] {kind} {spec['inst']} N={spec['N']} {spec['method']} "
                      f"{'' if kind == 'energy' else 'p=%.2e' % spec['level']} {dt:.1f}s", flush=True)
        np.save(os.path.join(OUT, f'raw_{kind}.npy'), np.array(results, dtype=object), allow_pickle=True)
    print('done')
