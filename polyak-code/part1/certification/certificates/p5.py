"""Exact source data for the central P5 branch at the three-cycle.

The source formulas are rebuilt here from normalized Chebyshev lags.  Sparse
coefficient arrays expose the actual polynomial equations and their identities.
The exporter derives the coefficient arrays in exact rational arithmetic.
"""
from __future__ import annotations

import sympy as sp
from .schema import polynomial, rational, rational_string


def export() -> dict:
    h, a, b, y, p, d, w2, w3 = sp.symbols("h A B y P D w2 w3")
    G, u, c = sp.symbols("G u c")
    variables = [h, a, b, y, p, d, w2, w3]
    R = sp.Rational
    q5 = 32*y**5-40*y**4+16*y**3-6*y**2-12*y+3
    qpoly = sp.Poly(q5, y)

    def reduce(expr):
        num, den = sp.fraction(sp.cancel(expr))
        return sp.rem(sp.Poly(num, y)*sp.invert(sp.Poly(den, y), qpoly), qpoly).as_expr()

    def lag(n, sign):
        gap = 1-c*c-u*u
        return (gap*(sp.chebyshevt(n,G)-sp.chebyshevt(n,c)) +
                sign*2*u*(1-c*c)*sp.chebyshevu(n-1,c))/sp.chebyshevu(n-1,G)

    x = -R(1,2)+h*b
    substitution = {G: 1+h, u: R(1,2)+h*a}
    def mean(expr):
        return (1-h*p)*expr.subs(c,x)+h*p*expr.subs(c,y)

    primal = [mean(lag(1,-1))+h*d] + [mean(lag(n,1))-h*d for n in (2,3,5)]
    dual_rational = sp.cancel(-(lag(1,-1)+w2*lag(2,1)+w3*lag(3,1)+(1-w2-w3)*lag(5,1))/(G-c))
    Q, Qden = sp.fraction(dual_rational)
    raw_regularized = [sp.cancel(expr.subs(substitution)/h) for expr in primal]
    F = [sp.fraction(expr)[0].expand() for expr in raw_regularized]
    F += [sp.expand(expr.subs(substitution)) for expr in
          (Q.subs(c,y),sp.diff(Q,c).subs(c,x),sp.diff(Q,c).subs(c,y))]
    F0 = [sp.expand(expr.subs(h,0)) for expr in F]

    values = {
        a: -R(34,151)*y**4-R(77,302)*y**3+R(27,604)*y**2-R(75,302)*y+R(693,1208),
        b: -R(2275,151)*y**4+R(16769,604)*y**3-R(29287,1208)*y**2+R(19977,1208)*y-R(7471,2416),
        d: -R(243,151)*y**4+R(2097,604)*y**3-R(1959,1208)*y**2+R(1773,1208)*y+R(4381,2416),
        p: -R(396330,1057)*y**4+R(1393863,2114)*y**3-R(2294121,4228)*y**2+R(1529793,4228)*y-R(501309,8456),
        w2: (36571392*y**4+15609088*y**3+5194992*y**2+22511544*y+10388100)/43243231,
        w3: (4987008*y**4+2128512*y**3+708408*y**2+3069756*y+25003776)/43243231,
    }
    values_w5 = sp.expand(1-values[w2]-values[w3])
    polys = {"q5": polynomial(q5,[y])}
    polys.update({"critical_"+str(k):polynomial(v,[y]) for k,v in values.items()})
    polys["critical_w5"] = polynomial(values_w5,[y])
    polys.update({"F"+str(i):polynomial(expr,variables) for i,expr in enumerate(F)})
    polys.update({"F0_"+str(i):polynomial(expr,variables[1:]) for i,expr in enumerate(F0)})
    equations_mod = [reduce(expr.subs(values, simultaneous=True)) for expr in F0]
    for i,expr in enumerate(equations_mod):
        if expr != 0:
            raise ArithmeticError(f"critical equation F0[{i}] is nonzero: {expr}")

    jacobian = sp.Matrix(F).jacobian(variables[1:]).subs(h,0)
    dual_block = jacobian.extract([4,5,6],[2,5,6])
    primal_block = jacobian.extract([0,1,2,3],[0,1,4,3])
    for name,block in (("dual",dual_block),("primal",primal_block)):
        polys[name+"_jacobian_det"] = polynomial(reduce(block.subs(values,simultaneous=True).det()),[y])
        for i in range(block.rows):
            for j in range(block.cols):
                polys[f"{name}_jacobian_{i}_{j}"] = polynomial(reduce(block[i,j].subs(values,simultaneous=True)),[y])

    Q0 = sp.Poly(sp.expand(Q.subs({G:1,u:R(1,2)}).subs(values,simultaneous=True)),c)
    quotient, remainder = sp.div(Q0,sp.Poly((c+R(1,2))**2*(c-y)**2,c))
    if any(reduce(coef) != 0 for coef in remainder.all_coeffs()):
        raise ArithmeticError("critical double-square dual factorization failed")
    for i,coef in enumerate(reversed(quotient.all_coeffs())):
        polys[f"dual_quotient_q{i}"] = polynomial(reduce(coef),[y])
        polys[f"normalized_dual_quotient_q{i}"] = polynomial(reduce(coef)/15,[y])

    def first_slack(n,sign):
        Y = (R(3,4)-y*y)*(1-sp.chebyshevt(n,y))+sign*(1-y*y)*sp.chebyshevu(n-1,y)
        if n%3 == 0:
            result = R(n*n,2)-sign*n*(values[b]+values[d])+values[p]*Y
        elif n%3 == 1 and sign == -1:
            result = R(n*n,2)+values[b]-3*values[a]-n*values[b]+n*values[d]+values[p]*Y
        elif n%3 == 2 and sign == 1:
            result = R(n*n,2)+values[b]-3*values[a]+n*values[b]-n*values[d]+values[p]*Y
        else:
            return None
        return reduce(result)
    for n in range(1,24):
        for sign in (-1,1):
            expr=first_slack(n,sign)
            if expr is not None:
                polys[f"first_slack_{n}_{'lower' if sign==-1 else 'upper'}"] = polynomial(expr,[y])

    checks = [{"id":"critical_equations","kind":"remainder-zero","passed":True,"count":7},
              {"id":"dual_double_square","kind":"remainder-zero","passed":True,"count":4}]
    return {
        "id":"p5", "variables":[str(v) for v in variables], "polynomials":polys,
        "rationals":{"dual_Q":rational(dual_rational,[G,u,w2,w3,c]),
                     **{f"regularized_primal_{i}":rational(expr,variables) for i,expr in enumerate(raw_regularized)}},
        "intervals":{"critical_y":["5797/25000","23189/100000"]},
        "checks":checks,
        "source":{"system":"part1:eq:p5system; B:eq:blowup", "unknown_order":[str(v) for v in variables[1:]],
                  "primal_order":["L1+d","U2-d","U3-d","U5-d"],
                  "dual_order":["Q(y)","Qprime(x)","Qprime(y)"]},
    }
