"""Theorem 10.17: certification in ball arithmetic (Arb via
python-flint, 200 bits) with the Krawczyk operator.

Unknowns x = (kappa, alpha L, beta); shift 0; u1 = 2pi*3/13, u2 = 2pi*2/13, K = 4. Equations:
F1 = det[[L1(u1), L1(u2)], [L4(u1), L4(u2)]] and F2, F3 = T'(u_i) with T = lam1*L1 + lam4*L_{-4},
(lam1, lam4) proportional to (-L4(u1), L1(u1)), where L1 and L4 are the lag functions of the lags 1 and -4.
The script then checks (E1)-(E4) of Theorem 10.13 and the membership in the gap I_4 with
enclosures valid on the whole Krawczyk box.

Usage:  python3 exact_313.py      (writes the Krawczyk box to verification/exact_313_box.txt)
"""
import os, sys
from flint import arb, arb_series, arb_mat, fmpq, ctx
def check(c, *msg):
    if not c:
        print('CHECK FAILED', *msg); sys.exit(1)
OUTDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'verification'); os.makedirs(OUTDIR, exist_ok=True)
ctx.prec = 200
PI = arb.pi(); K = 4; L = 13
U = [2*PI*3/L, 2*PI*2/L]
def S(v, order=2):  # constant series
    return arb_series([v], prec=order)
def xi(kap, y, beta):
    x = y/kap; A = 1+beta-(x+y)/2; B = (y-x)/2; den = 2*B*(1-beta)
    return ((B*B-(1-beta)**2-A*A)/den, 2*A*(1+beta)/den, -4*beta/den)
def theta_and_d(X, w):
    X0, X1, X2 = X; c = w.cos(); s = w.sin()
    Xi = X0+X1*c+X2*c*c; dXi = -s*(X1+2*X2*c)
    th = (Xi*(1/s)).atan()*(-1) + PI/2
    dth = -(dXi*s - Xi*c)/(Xi*Xi + s*s)
    return th, dth
def lam_and_d(X, n, w):
    th, dth = theta_and_d(X, w)
    return th.cos()-(n*w-th).cos(), -th.sin()*dth + (n*w-th).sin()*(n-dth)
def F(kap, y, beta):
    X = xi(kap, y, beta)
    a1, da1 = lam_and_d(X, 1, U[0]); a2, da2 = lam_and_d(X, 1, U[1])
    b1, db1 = lam_and_d(X, -K, U[0]); b2, db2 = lam_and_d(X, -K, U[1])
    l1, l4 = -b1, a1
    return [a1*b2-a2*b1, l1*da1+l4*db1, l1*da2+l4*db2]
def F_arb(v): return F(*v)
def jac_box(B):
    J = [[None]*3 for _ in range(3)]
    for j in range(3):
        v = [S(B[0]), S(B[1]), S(B[2])]
        v[j] = arb_series([B[j], 1], prec=2)
        Fv = F(*v)
        for i in range(3):
            c = Fv[i].coeffs(); J[i][j] = c[1] if len(c) > 1 else arb(0)
    return J
# starting point of the Newton iteration
x = [arb("83.53433"), arb("2.218909"), arb("0.622768")]
for it in range(40):
    Fx = F_arb([arb(v.mid()) for v in x])
    J = jac_box([arb(v.mid()) for v in x])
    Jm = arb_mat([[J[i][j].mid() for j in range(3)] for i in range(3)])
    d = Jm.solve(arb_mat([[f.mid()] for f in Fx]))
    x = [arb((x[i] - d[i,0]).mid()) for i in range(3)]
print("Newton point:", [v.str(20) for v in x])
print("residual:", [f.str(5) for f in F_arb(x)])
# Krawczyk on box of radius r
r = arb("1e-25")
B = [arb(v.mid(), r) for v in x]
J = jac_box(B); Jmid = arb_mat([[J[i][j].mid() for j in range(3)] for i in range(3)])
C = Jmid.inv(); C = arb_mat([[C[i,j].mid() for j in range(3)] for i in range(3)])
Fx = F_arb([arb(v.mid()) for v in x])
Kx = []
CF = C*arb_mat([[f] for f in Fx])
IJ = arb_mat([[ (1 if i==j else 0) - sum((C[i,k]*J[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)])
dX = arb_mat([[B[j]-arb(x[j].mid())] for j in range(3)])
M2 = IJ*dX
ok = True
for i in range(3):
    Ki = arb(x[i].mid()) - CF[i,0] + M2[i,0]
    inside = (Ki.lower() > B[i].lower()) and (Ki.upper() < B[i].upper())
    ok = ok and inside
    print("component", i, "K(B) rad =", Ki.rad().str(5), " box rad =", B[i].rad().str(5), " |K-mid| =", (Ki-arb(x[i].mid())).str(5), "inside" if inside else "NOT inside")
print("KRAWCZYK:", "unique zero in box" if ok else "FAILED")
open(os.path.join(OUTDIR, "exact_313_box.txt"), "w").write("\n".join(b.str(40) for b in B))

# ---------------- verification of (E1)-(E4) and gap membership on the box B ----------------
if not ok: sys.exit(1)
X = xi(*B)
def theta_ser(w, order):
    lo, hi = float(w.lower()), float(w.upper())
    X0, X1, X2 = X
    t = arb_series([w,1], prec=order); c = t.cos(); sn = t.sin()
    Xs = X0+X1*c+X2*c*c
    if lo >= 0.05 and hi <= float(PI)-0.05: return (Xs*sn.inv()).atan()*(-1) + PI/2
    if hi < 0.2 or lo > float(PI)-0.2:
        if not (Xs.coeffs()[0] < 0): raise ValueError("branch")
        return (sn*((Xs*(-1)).inv())).atan()*(-1) + PI
    raise ValueError("wide")
def lam_ser(n, w, order):
    th = theta_ser(w, order); t = arb_series([w,1], prec=order)
    return th.cos()-(t*n-th).cos()
def co(ser,k):
    c = ser.coeffs(); return c[k] if k < len(c) else arb(0)
def val(n,w): return co(lam_ser(n,w,1),0)
a1, b1 = val(1,U[0]), val(-K,U[0]); a2, b2 = val(1,U[1]), val(-K,U[1])
check(a1 > 0 and b1 < 0 and b2 > 0 and a2 < 0)  # u1 in A+, u2 in A-
l1, l4 = -b1/(a1-b1), a1/(a1-b1)                          # normalized left kernel, positive
check(l1 > 0 and l4 > 0)
print("lambda_1 =", l1.str(15), " lambda_-4 =", l4.str(15))
w1, w2 = -a2/(a1-a2), a1/(a1-a2)                          # w1*a1 + w2*a2 = 0, positive
check(w1 > 0 and w2 > 0)
th = [co(theta_ser(u,1),0) for u in U]
mins = None
for r in range(1, L):
    if r in (1, (-K) % L): continue
    v = w1*val(r,U[0]) + w2*val(r,U[1]); check(v > 0, 'residue', r)
    mins = v if mins is None or float(v) < float(mins) else mins
mn = w1*th[0].cos() + w2*th[1].cos(); check(mn > 0, 'minimizer slack')
print("(E3) min residue slack", mins.str(8), " minimizer slack", mn.str(8))
E4 = (U[0]-th[0]).sin()*(-K*U[1]-th[1]).sin() - (-K*U[0]-th[0]).sin()*(U[1]-th[1]).sin()
check(not E4.contains(0)); print("(E4) det =", E4.str(8))
th5 = co(theta_ser(2*PI/5,1),0); th4 = co(theta_ser(PI/2,1),0)
check(th5 > PI/5 and th4 > PI/4 and th[0] < U[0]/2)
print("gap: Theta(2pi/5)-pi/5 =", (th5-PI/5).str(6), " Theta(pi/2)-pi/4 =", (th4-PI/4).str(6), " dip depth at u1 =", (U[0]/2-th[0]).str(6))
lam = {1: l1, -K: l4}
def Tser(wb, order):
    return lam_ser(1,wb,order)*l1 + lam_ser(-K,wb,order)*l4
for u in U:
    sr = Tser(u,3); check(co(sr,0).contains(0) and co(sr,1).contains(0), 'touching'); print("T''(u)/2 =", co(sr,2).str(6))
def ball(a,b): return arb(a).union(arb(b))
stats={"d2":0,"val":0}
def neg_d2(lo,hi,depth):
    I=ball(lo,hi)
    try: okk = co(Tser(I,3),2) < 0
    except ValueError: okk=False
    if okk: stats["d2"]+=1; return True
    if depth==0: print("d2 FAIL",float(lo),float(hi)); return False
    m=(lo+hi)/2; return neg_d2(lo,m,depth-1) and neg_d2(m,hi,depth-1)
def neg_val(lo,hi,depth):
    I=ball(lo,hi); c=(lo+hi)/2; rr=ball(lo-c,hi-c)
    try:
        sc=Tser(c,2); s2=co(Tser(I,3),2); okk=(co(sc,0)+co(sc,1)*rr+s2*rr*rr) < 0
    except ValueError: okk=False
    if okk: stats["val"]+=1; return True
    if depth==0: print("val FAIL",float(lo),float(hi)); return False
    m=(lo+hi)/2; return neg_val(lo,m,depth-1) and neg_val(m,hi,depth-1)
D0=arb(fmpq(1,100)); DS=arb(fmpq(15,1000))
cuts=[("d2",arb(0),D0)]; prev=D0
for om in sorted(U,key=lambda z: float(z)):
    cuts.append(("val",prev,om-DS)); cuts.append(("d2",om-DS,om+DS)); prev=om+DS
cuts.append(("val",prev,PI))
allok=True
for kind,lo,hi in cuts:
    n0 = 64 if kind=="val" else 8
    for j in range(n0):
        a_=lo+(hi-lo)*j/n0; b_=lo+(hi-lo)*(j+1)/n0
        allok = (neg_d2(a_,b_,14) if kind=="d2" else neg_val(a_,b_,20)) and allok
    print("piece",kind,round(float(lo),5),round(float(hi),5),"ok" if allok else "FAILED")
print("leaf boxes",stats)
print("RESULT:", "EXACT POINT VERIFIED: (E1)-(E4) hold, q* in I_4, sigma(q*)=sigma_{1,-4}(q*)=0" if allok else "NOT VERIFIED")
if not allok: sys.exit(1)
