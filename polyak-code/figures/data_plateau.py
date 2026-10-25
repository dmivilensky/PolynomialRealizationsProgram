"""The single-harmonic plateau of 2/9 in the gap I_4 in the coordinates (a, D): the curves a_E, a_2,
max R of the edge symbol, an upper estimate of a_F by linear programs over admissible symbols with lags
in N_{2/9} cap [-54, 54], and the image of the plateau in the (alpha L, beta) plane (illustration data)."""
import sys, json, numpy as np
from math import pi, cos, sin, tan, floor
from scipy.optimize import brentq
import os; HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(os.path.join(HERE, '..', 'data'))
from plateau_tools import Fraction_edge, aF_est

J, KD, KG = 2, 9, 4
F = Fraction_edge(J, KD, KG)

def tuning_from_Xi(X0, X1, X2):
    """Inverse of the chart of Proposition 8.12(a): the tuning with the quadratic Xi."""
    a = -X2
    def f(beta):
        e = 1-beta; B = 2*beta/(a*e); A = X1*B*e/(1+beta)
        return (B*B-e*e-A*A)/(2*B*e)-X0
    bs = np.concatenate([np.linspace(1e-6, 0.99, 400), 1-np.logspace(-2, -12, 400)])
    v = [f(b) for b in bs]
    for i in range(len(bs)-1):
        if v[i]*v[i+1] < 0:
            beta = brentq(f, bs[i], bs[i+1], xtol=1e-15)
            e = 1-beta; B = 2*beta/(a*e); A = X1*B*e/(1+beta)
            s = 1+beta-A; y = s+B; x = s-B
            return y/x, y, beta
    return None

if __name__ == '__main__':
    Ds = np.linspace(-22, 24, 93)
    rows = []
    for D in Ds:
        aE = F.aE(D); nb = F.nbar(D)
        a2 = F.a2(D); mr = F.maxR_edge(D)
        lo = max(0.0, min(a2, aE)-1)
        af = aF_est(F, D, lo, max(mr, aE)+60, M=6, tol=0.02)
        rows.append(dict(D=D, aE=aE, nbar=nb, a2=a2, maxR=mr, aF=af))
        print(round(D, 2), round(aE, 2), round(a2, 2), round(af, 2), round(mr, 2), flush=True)
    img = []
    for D in np.linspace(-20, 22, 43):
        base = max(F.aE(D), [r for r in rows if abs(r['D']-D) == min(abs(rr['D']-D) for rr in rows)][0]['aF'])
        for a in base*np.logspace(0.002, 4, 60):
            X2 = -a; X1 = 1+D+2*a*F.c0; X0 = F.h0-(1+D)*F.c0-a*F.c0**2
            t = tuning_from_Xi(X0, X1, X2)
            if t: img.append(dict(D=D, a=a, kappa=t[0], aL=t[1], beta=t[2]))
    json.dump(dict(j=J, k=KD, K=KG, rows=rows, image=img), open('plateau_2_9.json', 'w'))
    print('ok')
