"""Theorem 10.16: rigorous ball-arithmetic verification
(Arb via python-flint, 200 bits) that a boundary tuning q~ = (kappa~, alpha L, beta) of Table 2 is L-regular
(Definition 10.1, conditions (R1)-(R3)) at the shift 0 and lies in the gap I_K.

kappa~ is enclosed as the root of det M(q(kappa), 0) in an exact rational bracket refined by bisection; the
dual weights are obtained by solving, for every tight class, one pair of lags exactly, with optional extra lags
of fixed positive rational weights. Every inequality is decided by a ball enclosure that does not contain 0.

Usage:  python3 verify_plateaus.py plateaus_cases.json NAME [delta_permille]
        (run_plateaus.py runs all thirty-five rows; the log of a row is written to verification/plateaus/)
        (NAME is a key of plateaus_cases.json, e.g. 3/13 or K5:2/11; the gap index K is part of the case data)
Case format (json): {"K":4,"aL":[num,den],"beta":[num,den],"L":L,"S":[j...],"pairs":[[n1,n2],...],
                     "extras":{"n":[num,den],...},"kb":[klo,khi]}
"""
import sys, json
from flint import arb, arb_series, arb_mat, fmpq, ctx
ctx.prec = 200
PI = arb.pi()
def check(c, *msg):
    if not c:
        print('CHECK FAILED', *msg, flush=True); sys.exit(1)
cases = json.load(open(sys.argv[1])); name = sys.argv[2]; C = cases[name]
L = C["L"]; K = C["K"]; Y = fmpq(*C["aL"]); BETA = fmpq(*C["beta"])
SJ = sorted(C["S"]); OM = [2*PI*j/L for j in SJ]; s = len(OM)
PAIRS = [tuple(p) for p in C["pairs"]]; REP = [p[0] for p in PAIRS]
EXTRAS = {int(n): fmpq(*v) for n, v in C.get("extras", {}).items()}
check(len(REP) == s and len({r % L for r in REP}) == s and 0 not in {r % L for r in REP}, "classes")
for n in EXTRAS: check(n % L in {r % L for r in REP} or n % L == 0, "extra outside classes", n)
ZERO = {n: v for n, v in EXTRAS.items() if n % L == 0}
def xi(kap):
    y = arb(Y); b = arb(BETA); x = y/kap
    A = 1+b-(x+y)/2; B = (y-x)/2; den = 2*B*(1-b)
    return ((B*B-(1-b)**2-A*A)/den, 2*A*(1+b)/den, -4*b/den)
class T:
    def __init__(self, kap): self.X = xi(kap)
    def theta(self, w, order):
        lo, hi = float(w.lower()), float(w.upper())
        X0, X1, X2 = self.X
        t = arb_series([w, 1], prec=order); c = t.cos(); sn = t.sin()
        X = X0+X1*c+X2*c*c
        if lo >= 0.002 and hi <= float(PI)-0.002: return PI/2-(X*sn.inv()).atan()
        if hi < 0.2 or lo > float(PI)-0.2:
            if not (X.coeffs()[0] < 0): raise ValueError("branch")
            return PI-(sn*(-X).inv()).atan()
        raise ValueError("wide")
    def lam(self, n, w, order):
        th = self.theta(w, order); t = arb_series([w, 1], prec=order)
        return th.cos()-(n*t-th).cos()
def co(ser, k):
    c = ser.coeffs(); return c[k] if k < len(c) else arb(0)
def val(Tq, n, w): return co(Tq.lam(n, w, 1), 0)
def dval(Tq, n, w): return co(Tq.lam(n, w, 2), 1)
def Mmat(Tq): return arb_mat([[val(Tq, r, w) for w in OM] for r in REP])
def ball(a, b): return arb(a).union(arb(b))
out = []
def say(*a):
    t = " ".join(str(x) for x in a); print(t, flush=True); out.append(t)
say("case", name, json.dumps(C))
# 1. kappa~ : sign change of det M on an exact rational bracket, refined by bisection
klo, khi = fmpq(*[int(round(C["kb"][0]*10**6)), 10**6]), fmpq(*[int(round(C["kb"][1]*10**6)), 10**6])
f = lambda k: Mmat(T(arb(k))).det()
flo, fhi = f(klo), f(khi)
check((flo*fhi) < 0, "bracket", flo, fhi)
for _ in range(110):
    km = (klo+khi)/2; fm = f(km)
    if (fm*flo) < 0: khi, fhi = km, fm
    elif (fm*flo) > 0: klo, flo = km, fm
    else: break
check((f(klo)*f(khi)) < 0)
KAP = ball(klo, khi); Tq = T(KAP)
check(float(KAP.rad()) < 1e-26, "bracket width")
say("kappa~ in", KAP.str(30, radius=True))
# gap membership I_K: Theta(2pi/(K+1))>pi/(K+1), Theta(2pi/K)>pi/K, anchor in the dip
th5 = co(Tq.theta(2*PI/(K+1), 1), 0); th4 = co(Tq.theta(2*PI/K, 1), 0)
check(th5 > PI/(K+1) and th4 > PI/K, "gap")
wa = OM[-1]
check(co(Tq.theta(wa, 1), 0) < wa/2, "anchor not in dip")
say("I_K: Theta(2pi/(K+1))-pi/(K+1) =", (th5-PI/(K+1)).str(6), "; Theta(2pi/K)-pi/K =", (th4-PI/K).str(6),
    "; anchor dip depth =", (wa/2-co(Tq.theta(wa, 1), 0)).str(6))
# 2. kernels: right kernel w (M w = 0) and left kernel mu (mu^T M = 0) by solving with one coordinate fixed
M = Mmat(Tq)
def kernel(Mx):
    n = s; best = None
    for drop in range(n):           # fix coordinate 'drop' = 1, drop one equation (row 'r'), solve the rest
        for r in range(n):
            A = arb_mat([[Mx[i, j] for j in range(n) if j != drop] for i in range(n) if i != r])
            b = arb_mat([[-Mx[i, drop]] for i in range(n) if i != r])
            try:
                d = A.det()
                if d.contains(0): continue
                x = A.solve(b)
            except Exception: continue
            v = []; k = 0
            for j in range(n):
                if j == drop: v.append(arb(1))
                else: v.append(x[k, 0]); k += 1
            return v
    return None
w = kernel(M); check(w is not None, "right kernel")
mu = kernel(M.transpose()); check(mu is not None, "left kernel")
sw = sum(w, arb(0)); sm = sum(mu, arb(0)); check(not sw.contains(0) and not sm.contains(0))
w = [x/sw for x in w]; mu = [x/sm for x in mu]
check(all(x > 0 for x in w) and all(x > 0 for x in mu), "kernel signs", w, mu)
# rank s-1 is implied by the nonsingular (s-1)x(s-1) minor used in kernel(); M w = 0 holds at the root kappa~
say("w* =", [x.str(8) for x in w]); say("mu* =", [x.str(8) for x in mu])
# 3. slope equations V m = t, then lambda
th = [co(Tq.theta(om, 1), 0) for om in OM]
V = arb_mat([[L*(r*OM[i]-th[i]).sin() for r in REP] for i in range(s)])
tv = arb_mat([[-(sum((mu[k]*dval(Tq, REP[k], OM[i]) for k in range(s)), arb(0)) + sum((arb(v)*dval(Tq, n, OM[i]) for n, v in ZERO.items()), arb(0)))] for i in range(s)])
dV = V.det(); check(not dV.contains(0), "det V")
m = V.solve(tv)
lam = {}
for k, (n1, n2) in enumerate(PAIRS):
    check((n2-n1) % L == 0 and n2 != n1, "pair class")
    j2 = (n2-n1)//L
    ex = [(n, v) for n, v in EXTRAS.items() if (n-n1) % L == 0]
    mu_k = mu[k]-sum((arb(v) for n, v in ex), arb(0))
    m_k = m[k, 0]-sum((arb(v)*((n-n1)//L) for n, v in ex), arb(0))
    l2 = m_k/j2; l1 = mu_k-l2
    lam[n1] = l1; lam[n2] = l2
    for n, v in ex: lam[n] = arb(v)
for n, v in ZERO.items(): lam[n] = arb(v)
check(len(lam) == 2*s+len(EXTRAS), "lag collision")
say("det V =", dV.str(6)); say("lambda* =", {n: v.str(6) for n, v in sorted(lam.items())})
check(all(v > 0 for v in lam.values()), "lambda sign")
# 4. (R1): other residues strict, minimizer slack
REPset = {x % L for x in REP}; mins = None
for r in range(1, L):
    if r in REPset: continue
    v = sum((w[i]*val(Tq, r, OM[i]) for i in range(s)), arb(0))
    check(v > 0, "R1 residue", r, v)
    mins = v if mins is None or float(v) < float(mins) else mins
mn = sum((w[i]*th[i].cos() for i in range(s)), arb(0)); check(mn > 0, "minimizer")
say("(R1): min slack of other residues", mins.str(6), "; minimizer slack", mn.str(6))
# 5. (R2)
tau = -1/sum(Tq.X, arb(0))
c0 = sum((l*n*(n+2*tau) for n, l in lam.items()), arb(0)); check(c0 > 0, "S''(0)")
P = [sum((l*(1-(n*om).cos()) for n, l in lam.items()), arb(0)) for om in OM]; check(all(p > 0 for p in P), "P")
say("sum lambda n(n+2tau) =", c0.str(6), "; min P* on S =", min(P, key=lambda z: float(z)).str(6))
LAMS = sorted(lam.items())
def Sser(wb, order):
    tot = None
    for n, l in LAMS:
        x = Tq.lam(n, wb, order)*l; tot = x if tot is None else tot+x
    return tot
for om in OM:
    sr = Sser(om, 2); check(co(sr, 0).contains(0) and co(sr, 1).contains(0), "S, S' at support")
stats = {"d2": 0, "val": 0}
def neg_d2(lo, hi, depth):
    I = ball(lo, hi)
    try: ok = co(Sser(I, 3), 2) < 0
    except ValueError: ok = False
    if ok: stats["d2"] += 1; return True
    if depth == 0: return False
    mid = (lo+hi)/2; return neg_d2(lo, mid, depth-1) and neg_d2(mid, hi, depth-1)
def neg_val(lo, hi, depth):
    I = ball(lo, hi); c = (lo+hi)/2; r = ball(lo-c, hi-c)
    try:
        sc = Sser(c, 2); s2 = co(Sser(I, 3), 2)
        ok = (co(sc, 0)+co(sc, 1)*r+s2*r*r) < 0
    except ValueError: ok = False
    if ok: stats["val"] += 1; return True
    if depth == 0: say("val FAIL", float(lo), float(hi)); return False
    mid = (lo+hi)/2; return neg_val(lo, mid, depth-1) and neg_val(mid, hi, depth-1)
D0 = arb(fmpq(1, 100)); DS0 = arb(fmpq(int(sys.argv[3]) if len(sys.argv) > 3 else 15, 1000))
DS0 = min([DS0] + [(OM[i+1]-OM[i])*fmpq(2, 5) for i in range(s-1)], key=lambda z: float(z))
def concave_radius(om):
    # largest delta in a fixed list (all <= DS0) on which S'' < 0 is certified on [om-delta, om+delta]
    for fr in (1, fmpq(2,3), fmpq(2,5), fmpq(1,4), fmpq(3,20), fmpq(1,10), fmpq(1,16), fmpq(1,25)):
        d = DS0*fr
        ok = all(neg_d2(om-d+2*d*j/8, om-d+2*d*(j+1)/8, 12) for j in range(8))
        if ok: return d
    return None
for fr0 in (1, fmpq(1,2), fmpq(1,4), fmpq(1,10), fmpq(1,25)):
    D0c = D0*fr0
    if all(neg_d2(D0c*j/8, D0c*(j+1)/8, 12) for j in range(8)): D0 = D0c; break
say("concavity radius at 0:", D0.str(4))
cuts = [("d2", arb(0), D0)]; prev = D0
for om in OM:
    d = concave_radius(om)
    check(d is not None, "no concavity radius at", om)
    cuts.append(("val", prev, om-d)); cuts.append(("d2", om-d, om+d)); prev = om+d
cuts.append(("val", prev, PI))
ok = True
nmax = max(abs(n) for n in lam)
for kind, lo, hi in cuts:
    check(float(hi) > float(lo), "cuts")
    n0 = max(64, int(float(hi-lo)*nmax*4)) if kind == "val" else 8
    for j in range(n0):
        a_ = lo+(hi-lo)*j/n0; b_ = lo+(hi-lo)*(j+1)/n0
        ok = (neg_d2(a_, b_, 16) if kind == "d2" else neg_val(a_, b_, 22)) and ok
        if not ok: break
    say("piece", kind, round(float(lo), 5), round(float(hi), 5), "ok" if ok else "FAILED")
    if not ok: break
say("leaf boxes:", stats)
say("RESULT:", name, ("VERIFIED: (q~,0) is %d-regular, q~ in I_K, sigma(q~)=0" % L) if ok else "NOT VERIFIED")
import os
LOGDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "verification", "plateaus")
os.makedirs(LOGDIR, exist_ok=True)
open(os.path.join(LOGDIR, "plateau_%s.log" % name.replace("/", "_").replace(":", "_")), "w").write("\n".join(out)+"\n")
if not ok: sys.exit(1)
