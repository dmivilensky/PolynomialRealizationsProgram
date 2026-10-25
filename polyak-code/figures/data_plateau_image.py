"""Image of the plateau of 2/9 in the (alpha L, beta) plane, from the boundary data of data_plateau.py."""
import sys, json, numpy as np
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from data_plateau import F, tuning_from_Xi
d = json.load(open('plateau_2_9.json'))
rows = d['rows']; Ds = np.array([r['D'] for r in rows]); low = np.array([max(r['aE'], r['aF']) for r in rows])
img = []
for D in np.linspace(Ds.min(), Ds.max(), 121):
    base = float(np.interp(D, Ds, low))
    for a in base*np.logspace(0.001, 4, 90):
        X2 = -a; X1 = 1+D+2*a*F.c0; X0 = F.h0-(1+D)*F.c0-a*F.c0**2
        t = tuning_from_Xi(X0, X1, X2)
        if t: img.append(dict(D=float(D), a=float(a), kappa=t[0], aL=t[1], beta=t[2]))
d['image'] = img
json.dump(d, open('plateau_2_9.json', 'w'))
print(len(img))
