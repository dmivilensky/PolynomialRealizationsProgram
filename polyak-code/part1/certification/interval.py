"""Outward-rounded continuation, with replayable exact rational proposals.

Floating point proposes a centre, radius and inverse. Arb alone accepts a
Krawczyk inclusion, contraction, connected branch and user-supplied signs.
Every accepted box retains the rational data needed for an independent replay.
"""
from dataclasses import dataclass
import sympy as s
from sympy.printing.pycode import PythonCodePrinter
import numpy as np
from scipy.optimize import root
from flint import arb, ctx as arb_context
from .certificates.schema import rational_string


class Printer(PythonCodePrinter):
    def _print_Rational(self, expr):
        return f"(arb({expr.p})/{expr.q})"


def funcs(expr, args):
    return s.lambdify(args, expr, modules=[{"arb":arb}], printer=Printer(), cse=True)


def ball(lo, hi):
    a, b = arb(str(lo)), arb(str(hi))
    return arb((a+b)/2, (b-a)/2)


def inside(a, b):
    return a.lower() > b.lower() and a.upper() < b.upper()


def exact_bounds(value):
    return [str(value.lower().fmpq()), str(value.upper().fmpq())]


@dataclass(frozen=True)
class ContinuationConfig:
    precision: int = 160
    radius_factor: int = 4


def _run(F, par, vs, grid, guess, check=None, name="branch", collector=None,
        config=ContinuationConfig()):
    n = len(vs)
    jac = s.Matrix(F).jacobian(vs)
    ff = s.lambdify((par,vs),F,"numpy",cse=True)
    jf = s.lambdify((par,vs),jac,"numpy",cse=True)
    fi, ji = funcs(F,(par,vs)), funcs(jac.tolist(),(par,vs))
    dp = funcs([s.diff(e,par) for e in F],(par,vs))
    accepted, previous = [], None

    def require(condition, label):
        if collector is not None:
            return collector.check(condition, name+": "+label, kind="arb")
        if not condition:
            raise ValueError(name+": "+label)

    for a,b in zip(grid[:-1],grid[1:]):
        mid = (a+b)/2
        solution = root(lambda x:ff(mid,x),guess,jac=lambda x:jf(mid,x),tol=1e-11)
        z = solution.x
        require(np.max(np.abs(ff(mid,z))) < 1e-7,"finite Newton proposal")
        guess = z
        inverse = np.linalg.inv(jf(mid,z))
        inverse_ball = [[arb(str(v)) for v in row] for row in inverse]
        parameter, centre = ball(a,b), [arb(str(v)) for v in z]
        slope = -inverse @ np.array([float(v.mid()) for v in dp(arb(str(mid)),centre)])
        radius = config.radius_factor*(b-a)/2*np.maximum(np.abs(slope),.05)+1e-10
        box = [arb(centre[i],arb(str(radius[i]))) for i in range(n)]
        J, f0, fp = ji(parameter,box), fi(arb(str(mid)),centre), dp(parameter,centre)
        defect = [[arb(int(i==j))-sum(inverse_ball[i][k]*J[k][j] for k in range(n))
                   for j in range(n)] for i in range(n)]
        image = [centre[i]-sum(inverse_ball[i][k]*f0[k] for k in range(n))
                 -(parameter-arb(str(mid)))*sum(inverse_ball[i][k]*fp[k] for k in range(n))
                 +sum(defect[i][j]*(box[j]-centre[j]) for j in range(n)) for i in range(n)]
        require(all(inside(image[i],box[i]) for i in range(n)),"strict Krawczyk inclusion")
        row_norm = [sum(abs(defect[i][j])*arb(str(radius[j]))/arb(str(radius[i]))
                        for j in range(n)) for i in range(n)]
        eta = arb(max(v.upper() for v in row_norm))
        require(eta < 1,"weighted contraction")
        pv = dp(parameter,box)
        derivative_centre = [-sum(inverse_ball[i][k]*pv[k] for k in range(n)) for i in range(n)]
        derivative_norm = arb(max((abs(derivative_centre[i])/arb(str(radius[i]))).upper() for i in range(n)))
        error = eta*derivative_norm/(1-eta)
        derivative = [arb(derivative_centre[i],error*arb(str(radius[i]))) for i in range(n)]
        if previous is not None:
            require(all(inside(previous[i],box[i]) for i in range(n)),"adjacent branch connection")
        end_value = fi(arb(str(b)),centre)
        previous = [centre[i]-sum(inverse_ball[i][k]*end_value[k] for k in range(n))
                    +sum(defect[i][j]*(box[j]-centre[j]) for j in range(n)) for i in range(n)]
        if check is not None:
            check(parameter,box,derivative)
        accepted.append({"a":float(a),"b":float(b),"center":z.tolist(),"radii":radius.tolist(),
                         "contraction":float(eta),
                         "exact":{"parameter":[rational_string(str(a)),rational_string(str(b))],
                                  "centre":[rational_string(str(v)) for v in z],
                                  "radii":[rational_string(str(v)) for v in radius],
                                  "inverse":[[rational_string(str(v)) for v in row] for row in inverse],
                                  "krawczyk":[exact_bounds(v) for v in image],
                                  "derivative":[exact_bounds(v) for v in derivative],
                                  "contraction":rational_string(eta.fmpq())}})
    return accepted


def run(F, par, vs, grid, guess, check=None, name="branch", collector=None,
        config=ContinuationConfig()):
    with arb_context.workprec(config.precision):
        return _run(F,par,vs,grid,guess,check,name,collector,config)
