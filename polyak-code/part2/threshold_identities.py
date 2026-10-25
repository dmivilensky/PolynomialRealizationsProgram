"""Symbolic verification of the algebraic identities used in the proofs of Sections 8-12
(Appendices E-I).

A line OK marks an identity that sympy reduces to zero exactly. A line OK* marks an identity in several
variables that is evaluated at the listed rational sample point to 40 significant digits, and the check of
equation (H.7) evaluates both sides with mpmath at 40 digits for four fractions; these lines check the
formulas as printed in the paper, whose proofs are analytic. A failed check prints CHECK FAILED and exits
with status 1.

Usage: python3 threshold_identities.py
"""
import sys
import sympy as sp
from sympy import sin, cos, tan, cot, pi, sqrt, Rational as Q, simplify, expand, series, symbols

def check(cond, *msg):
    if not cond:
        print('CHECK FAILED', *msg); sys.exit(1)

def ok(name, expr=0, num=None):
    e = sp.simplify(expr)
    if e != 0 and num is not None:
        e = sp.N(e.subs({kk_: (sp.Rational(str(vv_)) if isinstance(vv_, float) else vv_) for kk_, vv_ in num.items()}), 40)
        check(abs(e) < 1e-30, name, e)
        print('OK* ', name)
    else:
        check(e == 0, name, e)
        print('OK  ', name)

x, y, be, c, ka, h0s = symbols('x y beta c kappa h0', real=True)

# ---------------------------------------------------------------- Lemma 9.2
A = 1+be-(x+y)/2; B = (y-x)/2
Xi = (B**2-(1-be)**2-A**2+2*A*(1+be)*c-4*be*c**2)/(2*B*(1-be))
N = (y-(1+be)*(1-c))**2+(1-be)**2*(1-c**2)
M = (y-1-be)*(1+be-x)-(1-be)**2+(1+be)*(2+2*be-x-y)*c-4*be*c**2
ok('tongue: B^2-A^2 = (y-1-beta)(1+beta-x)', expand(B**2-A**2-(y-1-be)*(1+be-x)))
ok('tongue: Xi = M/((y-x)(1-beta))', Xi-M/((y-x)*(1-be)))
ok('tongue: M(y) = -N(c)', expand(M.subs(x, y)+N))
Mp = sp.diff(M, x)
ok("tongue: M(y)-yM' factorization", expand(M.subs(x, y)-y*Mp-(1-c)*(y*(1+be)-2*(1-2*be*c+be**2))))
Xinf = (1-c)*(y*(1+be)-2*(1-2*be*c+be**2))/(y*(1-be))
ok('tongue: eq:Xikappa', Xi.subs(x, y/ka)-(Xinf-N/(y*(1-be)*(ka-1))))
ok('Lemma 8.14: dXi/dkappa', sp.diff(Xi.subs(x, y/ka), ka)-N/(y*(1-be)*(ka-1)**2))
c0, s0 = symbols('c0 s0', real=True)
kjk = 1+((y-(1+be)*(1-c0))**2+(1-be)**2*s0**2)/((1-c0)*(y*(1+be)-2*(1-2*be*c0+be**2))-h0s*y*(1-be))
expr = (Xi.subs(x, y/ka).subs(c, c0)-h0s).subs(ka, kjk)
ok('tongue: Xi_q(c0) = h0 at kappa = kappa_{j/k}', sp.together(expr.subs(s0**2, 1-c0**2)).subs(s0, sqrt(1-c0**2)))

# ---------------------------------------------------------------- eq:Lambdapoly and Proposition 10.7
w = symbols('omega', positive=True)
Th = symbols('Theta', positive=True)
for n in [1, 2, 3, 5, -1, -2, -4, -7]:
    lam = cos(Th)-cos(n*w-Th)
    poly = (sin(Th)/sin(w))*((cos(Th)/sin(Th)*sin(w))*(1-sp.chebyshevt(abs(n), cos(w)))
                             - sp.sign(n)*(1-cos(w)**2)*sp.chebyshevu(abs(n)-1, cos(w)))
    ok(f'eq:Lambdapoly n={n}', sp.expand_trig(sp.expand(lam-poly)), num={w: 0.731, Th: 1.137})

# ---------------------------------------------------------------- Lemma H.1 and Theorem 11.2
d, nb, T2, ck, n, th, kk = symbols('delta nbar T2 cprime n vartheta k', real=True)
Thc = ck+nb/2*d+T2/2*d**2
L = 2*sin(ck+n*d/2)*sin(ck+n*d/2-Thc)
s = series(L, d, 0, 3).removeO()
ok('edgeid: slope, class b', s.coeff(d, 1)-sin(ck)*(n-nb))
ok('edgeid: curvature, class b', 2*s.coeff(d, 2)-(-2*sin(ck)*T2+cos(ck)*n*(n-nb)))
L0 = 2*sin(n*d/2)*sin(n*d/2-Thc)
s0_ = series(L0, d, 0, 3).removeO()
ok('edgeid: slope, class 0', s0_.coeff(d, 1)+n*sin(ck))
ok('edgeid: curvature, class 0', 2*s0_.coeff(d, 2)-cos(ck)*n*(n-nb))
n1 = nb-th*kk; n2 = nb+(1-th)*kk
Tq = (1-th)*L.subs(n, n1)+th*L.subs(n, n2)
sq = series(Tq, d, 0, 3).removeO()
ok('edge symbol: zero slope', sq.coeff(d, 1))
ok("edge criterion: F''(omega0)", -sq.coeff(d, 2)-(sin(ck)*T2-cos(ck)*kk**2*th*(1-th)/2))
ok('sum w_i (n_i-nbar)^2 = k^2 th(1-th)', expand((1-th)*(n1-nb)**2+th*(n2-nb)**2-kk**2*th*(1-th)))

# ---------------------------------------------------------------- Lemma 11.9
a, D, w0, k = symbols('a D omega0 k', positive=True)
cc0 = cos(w0); ss0 = sin(w0); hh0 = cot(pi/k)*ss0
Xad = hh0+(1+D)*(cos(w)-cc0)-a*(cos(w)-cc0)**2
Theta = sp.acot(Xad/sin(w))
T1v = sp.diff(Theta, w).subs(w, w0); T2v = sp.diff(Theta, w, 2).subs(w, w0)
sp_ = sin(pi/k)
Y = 1+D+cot(pi/k)*cot(w0)
X = hh0*(1+cc0**2)+(1+D)*ss0**2*cc0
num = {w0: 0.81, a: 3.7, D: -0.43, k: 9}
ok('nbar(D) = 2 sin^2 c (1+D+cot c cot w0)', 2*T1v-2*sp_**2*Y, num=num)
ok("Theta''(omega0)", T2v-(sp_**2*(2*a*ss0-X/ss0**3)+2*cot(pi/k)*sp_**4*Y**2), num=num)
thv = symbols('theta_v', positive=True)
F2 = sp_*(sp_**2*(2*a*ss0-X/ss0**3)+2*cot(pi/k)*sp_**4*Y**2)-cos(pi/k)*k**2*thv*(1-thv)/2
a2 = (cot(pi/k)*(1+cc0**2)/(2*ss0**3)+(1+D)*cc0/(2*ss0**2)
      - sin(pi/k)*cos(pi/k)*Y**2/ss0+cos(pi/k)*k**2*thv*(1-thv)/(4*ss0*sin(pi/k)**3))
ok("F''(omega0) = 2 s0 sin^3 c (a - a2(D))", F2-2*ss0*sp_**3*(a-a2), num={**num, thv: 0.37})
nn = symbols('n', real=True)
ok('(n-nbar)^2 - k^2 th(1-th) = (n-n1)(n-n2) + (1-2th)k(n-nbar)',
   expand((nn-nb)**2-kk**2*th*(1-th)-((nn-n1)*(nn-n2)+(1-2*th)*kk*(nn-nb))))
ok('h at omega0 equals cot c', (Xad/sin(w)).subs(w, w0)-cot(pi/k), num=num)

# eq:Tpp for the edge symbol, at a numerical point, with T formed from Theta and Psi
import mpmath as mp
mp.mp.dps = 40
def num_check_Tpp(j, kq, aa, DD):
    W0 = 2*mp.pi*j/kq; C0 = mp.cos(W0); S0 = mp.sin(W0); CP = mp.pi/kq; H0 = S0/mp.tan(CP)
    b = pow(j, -1, kq)
    nbar = 2*mp.sin(CP)**2*(1+DD+mp.cot(CP)*mp.cot(W0))
    m1 = mp.floor((nbar-b)/kq); N1 = int(b+m1*kq); N2 = N1+kq; TH = (nbar-N1)/kq
    lam = {N1: 1-TH, N2: TH}
    def Th(om):
        return mp.acot((H0+(1+DD)*(mp.cos(om)-C0)-aa*(mp.cos(om)-C0)**2)/mp.sin(om))
    def T(om):
        return sum(l*(mp.cos(Th(om))-mp.cos(nq*om-Th(om))) for nq, l in lam.items())
    Tpp = mp.diff(T, W0, 2)
    def Psi(cv):
        om = mp.acos(cv)
        P = sum(l*(1-mp.cos(nq*om)) for nq, l in lam.items()); Qs = sum(l*mp.sin(nq*om) for nq, l in lam.items())
        return mp.sin(om)*Qs/P
    Rc0 = -mp.diff(Psi, C0, 2)/2
    YY = 1+DD+mp.cot(CP)*mp.cot(W0)
    A2 = (mp.cot(CP)*(1+C0**2)/(2*S0**3)+(1+DD)*C0/(2*S0**2)-mp.sin(CP)*mp.cos(CP)*YY**2/S0
          + mp.cos(CP)*kq**2*TH*(1-TH)/(4*S0*mp.sin(CP)**3))
    lhs = Tpp; rhs = 4*mp.sin(CP)**3*S0*1*(Rc0-aa)
    check(abs(lhs-rhs) < mp.mpf(10)**-25, 'Tpp', lhs, rhs)
    check(abs(Rc0-A2) < mp.mpf(10)**-25, 'R(c0)=a2', Rc0, A2)
    check(abs(mp.diff(Psi, C0)-(1+DD)) < mp.mpf(10)**-25, "Psi'(c0)=1+D")
    check(abs(Psi(C0)-H0) < mp.mpf(10)**-25, 'Psi(c0)=h0')
for (j, kq, aa, DD) in [(2, 9, 130, 0.3), (3, 13, 300, -1.2), (2, 5, 40, 0.7), (5, 23, 900, 2.0)]:
    num_check_Tpp(j, kq, aa, DD)
print('OK  eq:Tpp, R(c0)=a2, Psi(c0)=h0, Psi\'(c0)=1+D (4 fractions, 40 digits)')

# ---------------------------------------------------------------- Theorem 11.6
z, e, yv = symbols('z e y', real=True)
cp = pi/kk; K1 = kk-1
Aexp = nb/2*d+T2/2*d**2+e*sin(cp)**2*d**2
Cexp = -K1*nb/2*d+K1**2*T2/2*d**2+e*sin(cp)**2*d**2
wa = K1+z*d
Phi = wa*(cos(cp+Aexp)-cos(2*cp+yv*d-cp-Aexp))+(cos(cp+Cexp)-cos(K1*(2*cp+yv*d)+cp+Cexp))
ser = series(Phi, d, 0, 3).removeO()
uu = kk*K1*cos(cp)/4; vv = sin(cp)/2; E = K1*kk*T2+2*kk*sin(cp)**2*e
ok('fan pairs: order 0 near 2c', sp.expand_trig(ser.coeff(d, 0)), num={kk: 9, nb: 0.4, T2: 1.3, e: 0.2, z: -0.7, yv: 3})
ok('fan pairs: order 1 near 2c', sp.expand_trig(ser.coeff(d, 1)), num={kk: 9, nb: 0.4, T2: 1.3, e: 0.2, z: -0.7, yv: 3})
Qt = uu*(yv**2-nb*yv)+vv*z*(yv-nb)-vv*E
for nums in [{kk: 9, nb: 0.4, T2: 1.3, e: 0.2, z: -0.7, yv: 3}, {kk: 13, nb: -2.1, T2: 0.3, e: -1.1, z: 2.5, yv: -5}]:
    ok('fan pairs: eq:Qyjk', ser.coeff(d, 2)/2-Qt, num=nums)
u0 = symbols('u')
Phi0 = wa*(cos(cp+Aexp)-cos(u0-cp-Aexp))+(cos(cp+Cexp)-cos(-K1*u0-cp-Cexp))
f1 = sp.diff(Phi0/2, u0).subs(u0, 0)
ok('fan pairs: f1 = -delta(u nbar + v z) + O(delta^2)', series(f1, d, 0, 2).removeO()+d*(uu*nb+vv*z),
   num={kk: 9, nb: 0.4, T2: 1.3, e: 0.2, z: -0.7})
aa_, bb_, EE = symbols('a b E', real=True)
Qg = aa_*(yv**2-nb*yv)+bb_*z*(yv-nb)-bb_*EE
zs = sp.solve(sp.Eq(Qg.subs(yv, n1), Qg.subs(yv, n2)), z)[0]
ok('fan pairs: v z_* = -u(nbar + k(1-2th))', bb_*zs+aa_*(nb+kk*(1-2*th)))
ok('fan pairs: common value u k^2 th(1-th) - v E', Qg.subs(yv, n1).subs(z, zs)-(aa_*kk**2*th*(1-th)-bb_*EE))
ok('fan pairs: vertex at (n1+n2)/2', sp.solve(sp.diff(Qg.subs(z, zs), yv), yv)[0]-(n1+n2)/2)
F2s = sin(cp)*T2-cos(cp)*kk**2*th*(1-th)/2
ok('fan pairs: u k^2 th(1-th) - vE = (k/2)(-(k-1)F\'\' - 2 sin^3 c e)',
   (uu*kk**2*th*(1-th)-vv*E)-(kk/2)*(-(kk-1)*F2s-2*sin(cp)**3*e))

# ---------------------------------------------------------------- Lemma H.2
for kq in range(3, 12):
    tq = symbols('t'); cpq = pi/kq
    Pk = kq*cos(cpq)-(kq-1)*cos(tq-cpq)-cos((kq-1)*tq+cpq)
    ok(f'Upsilon_k k={kq}: Y(0)=Y(2c)=0, Y\'\'=k(k-1)cos c',
       sp.Abs(Pk.subs(tq, 0))+sp.Abs(Pk.subs(tq, 2*cpq))+sp.Abs(sp.diff(Pk, tq, 2).subs(tq, 0)-kq*(kq-1)*cos(cpq))
       + sp.Abs(sp.diff(Pk, tq, 2).subs(tq, 2*cpq)-kq*(kq-1)*cos(cpq)), num={})

# ---------------------------------------------------------------- Lemma 11.7
cc = symbols('c', real=True)
C0 = hh0-1-cc0
Xad_c = hh0+(1+D)*(cc-cc0)-a*(cc-cc0)**2
ok('edge domain: 1+c-Xi = a(c-c0)^2 - D(c-c0) - C0', expand(1+cc-Xad_c-(a*(cc-cc0)**2-D*(cc-cc0)-C0)))
ok('edge domain: Xi(1)', expand(Xad_c.subs(cc, 1)-(hh0+(1+D)*(1-cc0)-a*(1-cc0)**2)))
ok('edge domain: Xi(-1)', expand(Xad_c.subs(cc, -1)-(hh0-(1+D)*(1+cc0)-a*(1+cc0)**2)))

# ---------------------------------------------------------------- Proposition 11.13
t = symbols('t', positive=True)
for (j, kq) in [(2, 9), (3, 13), (2, 5), (7, 30)]:
    W0 = 2*pi*j/kq; S0 = sin(W0); H0 = S0*cot(pi/kq)
    tinf = 2*tan(pi/(2*kq))/S0
    ok(f'location: t_inf root, {j}/{kq}', 4/tinf-S0**2*tinf-4*H0, num={})
    ok(f'location: sqrt(h0^2+s0^2) = s0/sin c, {j}/{kq}', sqrt(H0**2+S0**2)-S0/sin(pi/kq), num={})
    ok(f'location: 2-2c0 = 4 sin^2(pi j/k), {j}/{kq}', 2-2*cos(W0)-4*sin(pi*j/kq)**2, num={})

# ---------------------------------------------------------------- Proposition 10.15
for Kq in range(2, 9):
    WK = sp.cancel((1-sp.chebyshevt(Kq, c))/(1-c))
    check(sp.denom(sp.together(WK)).is_number, 'W_K polynomial', Kq)
    ok(f'twolag K={Kq}: W_K(1)=K^2', WK.subs(c, 1)-Kq**2)
    r = symbols('r', positive=True)
    Psi1 = sp.limit((1+c)*(1-r*sp.chebyshevu(Kq-1, c))/(1+r*WK), c, 1)
    ok(f'twolag K={Kq}: Psi(1)', Psi1-2*(1-r*Kq)/(1+r*Kq**2))
    om = symbols('om', positive=True)
    lhs = sp.chebyshevu(Kq-1, cos(om))+WK.subs(c, cos(om))
    rhs = sin(Kq*om/2)*sin((Kq+1)*om/2)/(sin(om/2)**2*cos(om/2))
    ok(f'twolag K={Kq}: U_(K-1)+W_K product form', lhs-rhs, num={om: 0.913})

# ---------------------------------------------------------------- Lemma I.1 and Proposition 12.4
m_, a_, t1, t2 = symbols('m a t1 t2', positive=True)
for mq in [4, 5, 6, 9]:
    wst = 2*pi/mq; cpq = pi/mq; T1n = cos(wst)
    om = symbols('om', positive=True)
    Xj = 1+cos(om)-a_*(cos(om)-T1n)*(cos(om)-t2)
    Thj = sp.acot(Xj/sin(om))
    d1 = sp.diff(Thj, om).subs(om, wst); d2 = sp.diff(Thj, om, 2).subs(om, wst)
    nm = {a_: Q(23, 10), t2: T1n-Q(31, 100)}
    ok(f'junction m={mq}: Theta(w*) = c', Thj.subs(om, wst)-cpq, num=nm)
    ok(f"junction m={mq}: Theta' - 1/2", d1-Q(1, 2)+a_*(T1n-t2)*sin(cpq)**2, num=nm)
    ok(f"junction m={mq}: Theta''", d2-(-cot(cpq)/2+a_/2*tan(cpq)*(2-T1n**2-T1n*t2)+2*d1**2*cot(cpq)), num=nm)
    g = a_*(T1n-t2)*sin(cpq)**2
    F2j = sin(cpq)*d2-(mq-2*g)*g*cos(cpq)
    rhs = g*cos(cpq)*(4*g-(mq+2)+2*(1-T1n)/(T1n-t2)+T1n/(1+T1n))
    ok("junction m=%d: F''(w*) in the form of the proof of Proposition 12.4" % mq, F2j-rhs, num=nm)
for mq in [4, 5]:
    um = 1-sin(pi/mq)**2/sin(pi/(mq-1))**2; tt = cos(2*pi/mq)
    val = sp.nsimplify(sp.simplify(4*um+2/um+tt/(1+tt)))
    ok(f'cornerineq m={mq}: value', val-(Q(22, 3) if mq == 4 else 4*sqrt(5)-1), num={})
# constants of the proof of Lemma I.2 for m >= 6 (exact comparisons of real constants)
PI = sp.pi
consts = [
    ('1 - pi^2/150 > 0.934', 1-PI**2/150-Q(934, 1000)),
    ('1/0.934 < 1.071', Q(1071, 1000)-1/Q(934, 1000)),
    ('1.071 (72 pi^2/150 + pi^4/720) <= 5.22', Q(522, 100)-Q(1071, 1000)*(72*PI**2/150+PI**4/720)),
    ('5.22/216 <= 0.0242', Q(242, 10000)-Q(522, 100)/216),
    ('2.0242 * 5.22 <= 10.57', Q(1057, 100)-Q(20242, 10000)*Q(522, 100)),
    ('8/6 + (36 + 6*10.57)/(72 - 6 - 10.57) + 1/2 < 3.63', Q(363, 100)-(Q(8, 6)+(36+6*Q(1057, 100))/(72-6-Q(1057, 100))+Q(1, 2))),
]
for name, v in consts:
    check(sp.N(v, 50) > 0, name)
    print('OK ', 'cornerineq:', name)
print('ALL SYMBOLIC CHECKS PASSED')
