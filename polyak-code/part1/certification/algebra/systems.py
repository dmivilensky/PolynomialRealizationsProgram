"""The source polynomial systems, constructed afresh without serialized objects.

The central equations are regular at h=0: divide the four primal equations
by h before clearing denominators. The remaining three equations impose dual
contact at the two atoms. All symbols and their order are explicit.
"""
from dataclasses import dataclass
from functools import lru_cache
import sympy as s

G, u, c, z, h = s.symbols("G u c z h")
A, B, y, P, D, w2, w3 = s.symbols("A B y P D w2 w3")


def L(m):
    return ((1-c*c-u*u)*(s.chebyshevt(m,G)-s.chebyshevt(m,c))
            - 2*u*(1-c*c)*s.chebyshevu(m-1,c))/s.chebyshevu(m-1,G)


def U(m):
    return ((1-c*c-u*u)*(s.chebyshevt(m,G)-s.chebyshevt(m,c))
            + 2*u*(1-c*c)*s.chebyshevu(m-1,c))/s.chebyshevu(m-1,G)


@dataclass(frozen=True)
class System:
    family: str
    parameter: object
    variables: tuple
    equations: tuple
    dual: object
    substitution: dict

    def tuple(self):
        """Explicit symbolic interface shared by all exact verification suites."""
        return self.parameter, list(self.variables), list(self.equations), self.dual, self.substitution


@lru_cache(None)
def build(family):
    if family == "p1":
        dual = -((1-c*c-u*u)*(2+z*c+z*z*(c*c-1))
                 - 2*u*z*(1-c*c)*(1+z*c))
        substitution = {u:1-z/2+z*z*A, c:z*z*B}
        equations = tuple(s.cancel(e.subs(substitution)/z**2).expand()
                          for e in (dual, s.diff(dual,c)))
        return System(family,z,(A,B),equations,dual,substitution)
    if family == "p2":
        x, p, d, weight = s.symbols("x p d W")
        mean = lambda e: (1-p)*e.subs(c,x)+p*e.subs(c,y)
        primal = (mean(L(1))+d, mean(U(2))-d, mean(U(3))-d)
        dual = s.cancel(-(L(1)+weight*U(2)+(1-weight)*U(3))/(G-c)).as_numer_denom()[0]
        contact = (dual.subs(c,y), s.diff(dual,c).subs(c,x), s.diff(dual,c).subs(c,y))
        equations = tuple(s.cancel(e).as_numer_denom()[0].expand() for e in primal)+tuple(map(s.expand,contact))
        return System(family,G,(u,x,y,p,d,weight),equations,dual,{})
    if family == "central":
        x, uv = -s.Rational(1,2)+h*B, s.Rational(1,2)+h*A
        mean = lambda e: (1-h*P)*e.subs(c,x)+h*P*e.subs(c,y)
        primal = [mean(L(1))+h*D]+[mean(U(m))-h*D for m in (2,3,5)]
        dual = s.cancel(-(L(1)+w2*U(2)+w3*U(3)+(1-w2-w3)*U(5))/(G-c)).as_numer_denom()[0]
        substitution = {G:1+h,u:uv,c:x}
        equations = tuple(s.cancel(e.subs({G:1+h,u:uv})/h).as_numer_denom()[0].expand() for e in primal)
        contact = (dual.subs(c,y),s.diff(dual,c).subs(c,x),s.diff(dual,c).subs(c,y))
        equations += tuple(s.expand(e.subs({G:1+h,u:uv})) for e in contact)
        return System(family,h,(A,B,y,P,D,w2,w3),equations,dual,substitution)
    raise ValueError(f"unknown family: {family}")


def p1():
    return build("p1").tuple()


def p2():
    return build("p2").tuple()


def central():
    return build("central").tuple()
