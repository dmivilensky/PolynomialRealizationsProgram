"""Data for the figure 'gapchart': classification of a grid of the gap I_K in the coordinates (a, r1, r2)
by the periodic programs of period at most LMAX at the shift 0.
Usage: python3 data_gapchart.py K a_values N OUT [LMAX]   (a_values: comma separated; 'l1.1' means a = 1.1 a_0)"""
import sys, json, numpy as np
from math import pi, cos
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from hbtools import PL_feasible
K = int(sys.argv[1]); avals = sys.argv[2].split(','); N = int(sys.argv[3]); OUT = sys.argv[4]
LMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 80
lo, hi = 1/(K+1), 1/K
res = {}
for av in avals:
    out = []
    for i in range(N):
        for j in range(N):
            p1 = lo+(hi-lo)*(i+0.5)/N; p2 = lo+(hi-lo)*(j+0.5)/N
            if p2 <= p1: continue
            r1, r2 = cos(2*pi*p2), cos(2*pi*p1)   # r1<r2
            a0 = 2/((1-r1)*(1-r2))
            a = a0*float(av[1:]) if av.startswith('l') else float(av)
            if a <= a0: out.append([p1, p2, -2, 0]); continue
            X = (1-a*r1*r2, 1+a*(r1+r2), -a)
            found = 0
            for L in range(2*K+1, LMAX+1):
                ok, (w, nu, t) = PL_feasible(X, L, 0.0, ret=True)
                if ok:
                    k = int(np.argmax(nu)); found = [L, float(w[k]/(2*pi))]; break
            out.append([p1, p2, 1 if found else 0, found if found else 0])
        print(av, i, flush=True)
    res[av] = out
json.dump(res, open(OUT, 'w'))
