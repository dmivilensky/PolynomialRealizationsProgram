"""Exact initialized-spiral source expressions and rational branch witnesses.

The source data are specified here independently of the old scripts. Algebraic
reduction uses two quadratic quotient fields. Interval witnesses keep the
physical positive q branch and never use a floating-point sign decision.
"""
from functools import lru_cache
from fractions import Fraction
from math import comb

import sympy as s

from .schema import polynomial, rational, rational_string

RHO, Q, LAMBDA = s.symbols("rho q lambda")
F = RHO**2 * (RHO**2 + 1) - 2*Q*RHO*(RHO**2-RHO+1) - Q**2*(RHO**2+1)


def _quotient(expr, variable, modulus, domain):
    numerator, denominator = s.fraction(s.cancel(expr))
    n = s.Poly(numerator, variable, domain=domain)
    d = s.Poly(denominator, variable, domain=domain)
    p = s.Poly(modulus, variable, domain=domain)
    return (n * s.invert(d, p)).rem(p).as_expr()


def _conjugate(expr):
    return expr.subs(LAMBDA, RHO**2/LAMBDA, simultaneous=True)


@lru_cache(maxsize=None)
def _real(expr):
    e1 = -2*RHO**2/(RHO**2+1)
    result = _quotient((expr + _conjugate(expr))/2, LAMBDA,
                       LAMBDA**2-e1*LAMBDA+RHO**2, s.QQ.frac_field(RHO, Q))
    if result.has(LAMBDA):
        raise ValueError("requested real expression is not symmetric")
    return s.factor(result)


@lru_cache(maxsize=None)
def reduce_physical(expr):
    """Return polynomials A,B,D with expr=(A+B*q)/D on F=0."""
    reduced = _quotient(expr, Q, F, s.QQ.frac_field(RHO))
    a = s.cancel(reduced.subs(Q, 0))
    b = s.cancel(s.diff(reduced, Q))
    denominator = s.lcm(s.denom(a), s.denom(b))
    a, b = s.cancel(a*denominator), s.cancel(b*denominator)
    common = s.lcm([s.denom(c) for p in (a, b, denominator)
                    for c in s.Poly(p, RHO).all_coeffs()])
    a, b, denominator = [s.Poly(s.expand(p*common), RHO, domain=s.ZZ).as_expr()
                         for p in (a, b, denominator)]
    if s.LC(s.Poly(denominator, RHO)) < 0:
        a, b, denominator = -a, -b, -denominator
    return a, b, denominator


@lru_cache(maxsize=1)
def source():
    """The 44 exact inequalities, before any sign-certificate annotations."""
    r, q, z = RHO, Q, LAMBDA
    multiplier = (z+q**2/z)/(2*q)
    defect = q/2*(1-1/z)
    gap = 2*r*(r*r-r+1)/(r*r+1)**2
    hyperbolic = (r+1/r)/2
    constant = gap*(r*r-1)/(r*r+1)
    value = (constant+2*_real(multiplier))/4
    alpha = {-1: _conjugate(defect)*(multiplier+1)/2,
              1: _conjugate(defect)*(multiplier-1)/2}
    a = {-1: gap/(4*hyperbolic*r), 1: gap*r/(4*hyperbolic)}
    beta = {-1: gap*hyperbolic*_conjugate(z)/r+alpha[-1],
             1: gap*hyperbolic*z/r+alpha[1]}
    gamma = {-1: gap*r/(4*hyperbolic)-_real(alpha[-1])-_real(defect*_conjugate(defect))/4,
              1: gap/(4*hyperbolic*r)-_real(alpha[1])-_real(defect*_conjugate(defect))/4}
    normsq = {sign: _real(b*_conjugate(b)) for sign, b in beta.items()}
    reserve = (1-q**4)**2
    epsilon = s.Rational(3,40)*(r*r-1)*(r+1)**2/(r*(r*r+1))
    checks = []

    def add(name, expr, lo, hi):
        checks.append((name, s.cancel(expr), s.Rational(lo), s.Rational(hi)))

    for sign in (-1, 1):
        label = "lower" if sign == -1 else "upper"
        add(f"I.{label}.constant", gamma[sign]+reserve, "33/100", 1)
        add(f"I.{label}.norm", (gamma[sign]+reserve)**2-normsq[sign], "33/100", 1)
        add(f"II.{label}.beta", 1-normsq[sign], 1, "6/5")
        quadratic = a[sign]-epsilon
        add(f"II.{label}.quadratic", quadratic, 1, "6/5")
        for residue in range(3):
            linear = _real(beta[sign]*(z/r)**residue)+epsilon
            const = gamma[sign]+reserve
            add(f"II.{label}.{residue}.at_one", quadratic+linear+const, 1, "6/5")
            vertex = (sign, residue) in {(-1,0), (-1,1), (1,2)}
            expr = 2*quadratic+linear if vertex else 4*quadratic*const-linear**2
            add(f"II.{label}.{residue}.{'derivative' if vertex else 'discriminant'}",
                expr, 1, "6/5")
        add(f"III.{label}.derivative", 4*a[sign]**2*r**20-normsq[sign], "6/5", "1713/1000")
        tail = a[sign]*r**20+gamma[sign]+reserve
        add(f"III.{label}.constant", tail, "6/5", "1713/1000")
        add(f"III.{label}.norm", tail**2-normsq[sign]*r**20, "6/5", "1713/1000")
    initial_gradient = multiplier+defect
    for k in range(1, 10):
        zk = z**k
        discrepancy = value*r**(2*k)-value-_real(
            _conjugate(initial_gradient+multiplier*zk)*(zk-1))/2
        radius = _real((zk-1)*_conjugate(zk-1)-
                       (multiplier*zk-initial_gradient)*_conjugate(multiplier*zk-initial_gradient))/4
        radius += (1-(-q*q)**((k+1)//2))**2
        add(f"III.k{k}.lower", radius-discrepancy, "6/5", "1713/1000")
        add(f"III.k{k}.upper", radius+discrepancy, "6/5", "1713/1000")
    if len(checks) != 44:
        raise ValueError(f"expected 44 source inequalities, found {len(checks)}")
    return tuple(checks)


def export():
    """Canonical exact source data; the caller adds schema and source provenance."""
    return {"master_polynomial": polynomial(F, (RHO,Q)),
            "branch": "rho>0,q>0,F(rho,q)=0",
            "checks": [{"name": name, "interval": [rational_string(lo), rational_string(hi)],
                        "source": rational(expr, (RHO,Q)),
                        "witness_method": "integer-horner-physical-branch-v1",
                        "witness_scale": "18446744073709551616",
                        "numerator_witness": integer_numerator_witness(expr,lo,hi),
                        "reduced": {"constant": polynomial(a, (RHO,)),
                                    "linear": polynomial(b, (RHO,)),
                                    "denominator": polynomial(d, (RHO,))}}
                       for name, expr, lo, hi in source()
                       for a,b,d in [reduce_physical(expr)]]}


def _coefficients(expr):
    p = s.Poly(expr, RHO, domain=s.QQ)
    return [Fraction(p.nth(j)) for j in range(max(0,p.degree())+1)] if not p.is_zero else [Fraction(0)]


def bernstein_bounds(coeffs, lo, hi):
    """Exact rational Bernstein enclosure on a closed interval."""
    from flint import fmpq, fmpq_poly
    lo, hi = Fraction(lo), Fraction(hi)
    n = len(coeffs)-1
    p=fmpq_poly([fmpq(c.numerator,c.denominator) for c in coeffs])
    width=hi-lo
    affine=fmpq_poly([fmpq(lo.numerator,lo.denominator),fmpq(width.numerator,width.denominator)])
    shifted=p(affine)
    bs=[sum((shifted[j]*fmpq(comb(k,j),comb(n,j)) for j in range(k+1)),fmpq(0))
        for k in range(n+1)]
    return Fraction(str(min(bs))),Fraction(str(max(bs)))


def _mul_interval(a,b):
    corners = [x*y for x in a for y in b]
    return min(corners),max(corners)


def q_box(lo,hi,bits=48):
    """Rational enclosure of physical q throughout [lo,hi], certified by F signs."""
    lo,hi = Fraction(lo),Fraction(hi)
    # q is increasing as a function of rho on this positive branch. Avoid
    # relying only on pointwise endpoint signs: check the polynomials on ALL rho.
    def isolate(r):
        lower,upper = Fraction(0),Fraction(4)
        for _ in range(bits):
            mid=(lower+upper)/2
            f=r*r*(r*r+1)-2*mid*r*(r*r-r+1)-mid*mid*(r*r+1)
            if f>0: lower=mid
            else: upper=mid
        return lower,upper
    lower,upper=isolate(lo)[0],isolate(hi)[1]
    # Rounding outwards adds only a controlled dyadic unit and avoids endpoint
    # equality from a rational root; the Bernstein signs certify the full slab.
    unit=Fraction(1,2**(bits-2))
    for _ in range(12):
        lower=max(unit,lower-unit)
        upper+=unit
        lf=bernstein_bounds(_coefficients(F.subs(Q,s.Rational(lower))),lo,hi)[0]
        uf=bernstein_bounds(_coefficients(F.subs(Q,s.Rational(upper))),lo,hi)[1]
        if lf>=0 and uf<=0:
            return lower,upper
    raise ArithmeticError("slab too wide for direct physical-branch enclosure")


def branch_witness(a,b,d,lo,hi,max_depth=24):
    """A dyadic slab tree of exact positive physical-branch enclosures."""
    ac,bc,dc=map(_coefficients,(a,b,d))
    def visit(left,right,depth):
        box=q_box(left,right)
        ai=bernstein_bounds(ac,left,right)
        bi=bernstein_bounds(bc,left,right)
        di=bernstein_bounds(dc,left,right)
        product=_mul_interval(bi,box)
        if ai[0]+product[0]>0 and di[0]>0:
            return {"q_interval": [str(box[0]),str(box[1])]}
        if depth==0:
            raise ArithmeticError(f"insufficient branch resolution on {left},{right}")
        mid=(left+right)/2
        return {"left": visit(left,mid,depth-1), "right": visit(mid,right,depth-1)}
    return visit(Fraction(lo),Fraction(hi),max_depth)


def numerator_witness(expr,lo,hi,max_depth=24):
    """Certify the original bivariate numerator without high-degree field reduction."""
    numerator,denominator=s.fraction(s.cancel(expr))
    p=s.Poly(numerator,Q)
    cs=[_coefficients(p.nth(j)) for j in range(p.degree()+1)]
    def visit(left,right,depth):
        try:
            box=q_box(left,right,bits=32)
            result=(Fraction(0),Fraction(0))
            for c in reversed(cs):
                ci=bernstein_bounds(c,left,right)
                product=_mul_interval(result,box)
                result=ci[0]+product[0],ci[1]+product[1]
            if result[0]>0:
                return {"q_interval": [str(box[0]),str(box[1])]}
        except ArithmeticError:
            pass
        if depth==0:
            raise ArithmeticError(f"insufficient bivariate resolution on {left},{right}")
        mid=(left+right)/2
        return {"left":visit(left,mid,depth-1),"right":visit(mid,right,depth-1)}
    return visit(Fraction(lo),Fraction(hi),max_depth)


def integer_source(expr):
    numerator,_=s.fraction(s.cancel(expr))
    p=s.Poly(numerator,Q)
    result=[]
    for j in range(p.degree()+1):
        cs=_coefficients(p.nth(j))
        if any(c.denominator!=1 for c in cs):
            raise ValueError("numerator has a noninteger coefficient")
        result.append([c.numerator for c in cs])
    return result


def _scaled_bounds(lo,hi,scale):
    lo,hi=Fraction(lo)*scale,Fraction(hi)*scale
    return lo.numerator//lo.denominator,-((-hi.numerator)//hi.denominator)


def _integer_mul(a,b,scale):
    corners=[x*y for x in a for y in b]
    return min(corners)//scale,-((-max(corners))//scale)


def integer_numerator_witness(expr,lo,hi,max_depth=24,scale=2**64):
    """Compact dyadic tree certified by outward-rounded integer interval evaluation."""
    cs=integer_source(expr)
    def visit(left,right,depth):
        try:
            box=q_box(left,right,bits=32)
            ri,qi=_scaled_bounds(left,right,scale),_scaled_bounds(*box,scale)
            result=(0,0)
            for coefficient in reversed(cs):
                ci=(0,0)
                for c in reversed(coefficient):
                    prod=_integer_mul(ri,ci,scale)
                    ci=(c*scale+prod[0],c*scale+prod[1])
                prod=_integer_mul(qi,result,scale)
                result=(ci[0]+prod[0],ci[1]+prod[1])
            if result[0]>0:
                return {"q_interval":[str(box[0]),str(box[1])]}
        except ArithmeticError:
            pass
        if depth==0:
            raise ArithmeticError(f"insufficient integer resolution on {left},{right}")
        mid=(left+right)/2
        return {"left":visit(left,mid,depth-1),"right":visit(mid,right,depth-1)}
    return visit(Fraction(lo),Fraction(hi),max_depth)


