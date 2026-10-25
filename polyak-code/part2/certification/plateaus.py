"""Exact rational proposals for the two selected regular plateau examples.

The exporter deliberately uses the shorter dual witnesses without auxiliary
lags.  All decisions below use rational interval arithmetic; floating point is
used only to propose cosine boxes and the initial scalar root location.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json


def q(x):
    x = F(x)
    return [x.numerator, x.denominator]


class I:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ValueError('reversed interval')

    @staticmethod
    def of(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, other):
        b = I.of(other)
        return I(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I.of(other)

    def __rsub__(self, other):
        return I.of(other) + -self

    def __mul__(self, other):
        b = I.of(other)
        v = [self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi]
        return I(min(v), max(v))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = I.of(other)
        if b.lo <= 0 <= b.hi:
            raise ValueError('division by an interval containing zero')
        return self * I(1/b.hi, 1/b.lo)

    def __rtruediv__(self, other):
        return I.of(other) / self

    def __pow__(self, n):
        if n == 0:
            return I(1)
        if n % 2 == 0:
            a = self ** (n//2)
            vals = [a.lo*a.lo, a.hi*a.hi]
            return I(0 if a.lo <= 0 <= a.hi else min(vals), max(vals))
        return self * self ** (n-1)

    def json(self):
        return [q(self.lo), q(self.hi)]


def rounded(a,digits=14):
    scale=10**digits
    lo=(a.lo.numerator*scale)//a.lo.denominator
    hi=-((-a.hi.numerator*scale)//a.hi.denominator)
    return I(F(lo,scale),F(hi,scale))


def det(m):
    if len(m) == 0:
        return I(1)
    return sum(((-1)**j*m[0][j]*det([r[:j]+r[j+1:] for r in m[1:]])
                for j in range(len(m))), I(0))


def adj(m):
    n = len(m)
    return [[(-1)**(i+j)*det([r[:i]+r[i+1:] for k,r in enumerate(m) if k != j])
             for j in range(n)] for i in range(n)]


def solve(m, v):
    d = det(m)
    return [sum((a*b for a,b in zip(row,v)), I(0))/d for row in adj(m)]


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(a,b):
    return trim([(a[i] if i < len(a) else F(0)) +
                 (b[i] if i < len(b) else F(0)) for i in range(max(len(a),len(b)))])


def scale(a,t):
    return [x*t for x in a]


def mul(a,b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def derivative(a, order=1):
    for _ in range(order):
        a = [i*a[i] for i in range(1,len(a))] or [F(0)]
    return a


def evaluate(a,x):
    z = I(0)
    for c in reversed(a):
        z = z*x+c
    return z


def cheb(n, kind):
    a,b = [F(1)], [F(0),F(1 if kind == 'T' else 2)]
    if n == 0:
        return a
    for _ in range(1,n):
        a,b = b,add([F(0)]+scale(b,2),scale(a,-1))
    return b


def quotient(n):
    # (1-T_n)/(1-c), exact synthetic division at c=1.
    p = scale(cheb(n,'T'),-1)
    p[0] += 1
    out = [F(0)]*n
    for i in range(n-1,-1,-1):
        out[i] = -p[i+1]+(out[i+1] if i+1 < n else 0)
    assert out[0] == p[0]
    return out


def bernstein(p,a,b,degree=None):
    n = max(len(p)-1,degree or 0)
    power = [sum((p[k]*comb(k,j)*a**(k-j)*(b-a)**j
                  for k in range(j,len(p))), F(0)) for j in range(n+1)]
    return [sum((power[j]*F(comb(i,j),comb(n,j))
                 for j in range(i+1)), F(0)) for i in range(n+1)]


def xi(kappa,y,beta):
    x = y/kappa
    A = 1+beta-(x+y)/2
    B = (y-x)/2
    den = 2*B*(1-beta)
    return [(B**2-(1-beta)**2-A**2)/den,
            2*A*(1+beta)/den, -4*beta/den]


def lag_components(n):
    a = abs(n)
    W = quotient(a)
    return [W,[F(0)]+W,[F(0),F(0)]+W,
            scale(mul([F(1),F(1)],cheb(a-1,'U')),-1 if n > 0 else 1)]


def lag_value(n,X,c,order=0,quotiented=False):
    p = lag_components(n)
    if not quotiented:
        p = [mul([F(1),-F(1)],a) for a in p]
    vals = [evaluate(derivative(a,order),c) for a in p]
    return sum((X[i]*vals[i] for i in range(3)), vals[3])


def kernels(X,cs,reps):
    M = [[rounded(lag_value(r,X,c)) for c in cs] for r in reps]
    A = adj(M)
    # Both selected matrices have a nonzero (0,0)-minor.  Fix the
    # zeroth coordinate through the adjugate, then normalize its sum.
    right = [A[i][0] for i in range(len(cs))]
    left = A[0]
    right = [rounded(v/sum(right,I(0))) for v in right]
    left = [rounded(v/sum(left,I(0))) for v in left]
    return M,right,left


def weights(X,cs,reps,pairs):
    M,rho,mu = kernels(X,cs,reps)
    L = abs(pairs[0][1]-pairs[0][0])
    # d/dc G_{r+tL}(c_j)=G'_r(c_j)+tL*(T_r-Xi*U_{r-1}).
    pinning = [[rounded(L*(evaluate(cheb(abs(r),'T'),c)-
               (1 if r>0 else -1)*sum((X[i]*c**i for i in range(3)),I(0))*
               evaluate(cheb(abs(r)-1,'U'),c))) for r in reps] for c in cs]
    # Enforce the derivative equations directly. This uses ordinary polynomial
    # derivatives and does not need a numerical equality at a rational angle.
    V = [[rounded(lag_value(n2,X,c,1)-lag_value(n1,X,c,1))
          for n1,n2 in pairs] for c in cs]
    rhs = [rounded(-sum((mu[i]*lag_value(r,X,c,1) for i,r in enumerate(reps)),I(0))) for c in cs]
    moments = list(map(rounded,solve(V,rhs)))
    lam = {}
    for i,(n1,n2) in enumerate(pairs):
        lam[n2] = moments[i]
        lam[n1] = mu[i]-lam[n2]
    return M,rho,mu,V,lam,rhs,moments,pinning


def symbol_bernstein(X,lam,a,b,order=0):
    comps = [(n,[derivative(p,order) for p in lag_components(n)]) for n in lam]
    degree = max(len(p)-1 for _,ps in comps for p in ps)
    out = [I(0)]*(degree+1)
    for n,ps in comps:
        bs = [bernstein(p,a,b,degree) for p in ps]
        for j in range(degree+1):
            val = sum((X[i]*bs[i][j] for i in range(3)),I(bs[3][j]))
            out[j] += lam[n]*val
    return out


def _cos_box(j,L,digits=14):
    # Candidate only. A consumer must prove the actual cosine belongs to it.
    import mpmath as mp
    mp.mp.dps = digits+30
    d = 10**digits
    v = int(mp.floor(mp.cos(2*mp.pi*j/L)*d))
    return I(F(v-1,d),F(v+2,d))


def build_payload():
    cases = json.loads((Path(__file__).parents[1]/'plateaus'/'plateaus_cases.json').read_text())
    out = {'schema':'heavy-ball-selected-plateaus-v1','rows':[]}
    for name,root in [('2/9',F(10055082118856557,10**14)),
                      ('5/21',F(10680551194382778,10**14))]:
        C=cases[name]
        y,beta=F(*C['aL']),F(*C['beta'])
        # A modest isolating interval is sufficient. It deliberately avoids
        # treating the printed many-digit expansion as a certification goal.
        kap=I(root-F(1,10**7),root+F(1,10**7))
        cs=[_cos_box(j,C['L']) for j in C['S']]
        reps=[p[0] for p in C['pairs']]
        X=list(map(rounded,xi(kap,I(y),I(beta))))
        M,rho,mu,V,lam,rhs,moments,pinning=weights(X,cs,reps,C['pairs'])
        rho=list(map(rounded,rho));mu=list(map(rounded,mu))
        lam={n:rounded(v) for n,v in lam.items()}
        if not all(v.lo>0 for v in rho+mu+list(lam.values())):
            raise ValueError('nonpositive proposed kernel or dual weight')
        endpoint=[det(kernels(xi(I(k),I(y),I(beta)),cs,reps)[0])
                  for k in [kap.lo,kap.hi]]
        if not ((endpoint[0].hi<0<endpoint[1].lo) or
                (endpoint[1].hi<0<endpoint[0].lo)):
            raise ValueError('determinant root sign proposal failed')
        inactive={r:sum((rho[i]*lag_value(r,X,c) for i,c in enumerate(cs)),I(0))
                  for r in range(1,C['L']) if r not in {n % C['L'] for n in reps}}
        minimizer=sum((rho[i]*sum((X[k]*c**k for k in range(3)),I(0))
                       for i,c in enumerate(cs)),I(0))
        if not all(v.lo>0 for v in list(inactive.values())+[minimizer]):
            raise ValueError('primal strict slack proposal failed')
        radius=F(1,200)
        near=[I(c.lo-radius,c.hi+radius) for c in cs]
        cells=[]
        def cover(a,b,kind):
            vals=symbol_bernstein(X,lam,a,b,2 if kind=='curvature' else 0)
            if max(v.hi for v in vals)<0:
                cells.append({'lo':q(a),'hi':q(b),'kind':kind})
                return
            if b-a<F(1,2**24):
                raise ValueError('polynomial symbol cover failed')
            mid=(a+b)/2
            cover(a,mid,kind);cover(mid,b,kind)
        prev=F(-1)
        for c in reversed(near):
            cover(prev,c.lo,'value')
            cover(c.lo,c.hi,'curvature')
            prev=c.hi
        cover(prev,F(1),'value')
        out['rows'].append({'name':name,'gap':4,'y':q(y),'beta':q(beta),
            'period':C['L'],'numerators':C['S'],'pairs':C['pairs'],
            'kappa_bracket':kap.json(),'cosine_boxes':[c.json() for c in cs],
            'xi_boxes':[v.json() for v in X],
            'matrix_boxes':[[v.json() for v in r] for r in M],
            'slope_matrix_boxes':[[v.json() for v in r] for r in V],
            'pinning_matrix_boxes':[[v.json() for v in r] for r in pinning],
            'slope_target_boxes':[v.json() for v in rhs],
            'slope_moment_boxes':[v.json() for v in moments],
            'near_radius':q(radius),'symbol_cells':cells,
            'right_kernel_boxes':[v.json() for v in rho],
            'left_kernel_boxes':[v.json() for v in mu],
            'determinant_endpoint_boxes':[v.json() for v in endpoint],
            'rank_minor_box':adj(M)[0][0].json(),
            'slope_determinant_box':det(V).json(),
            'pinning_determinant_box':det(pinning).json(),
            'inactive_residue_boxes':{str(n):v.json() for n,v in inactive.items()},
            'minimizer_box':minimizer.json(),
            'dual_weight_boxes':{str(n):v.json() for n,v in lam.items()}})
    return out
