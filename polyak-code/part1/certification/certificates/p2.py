"""Exact P2 source formulas and mathematical certificate data.

Coefficients implement the rational arc in Appendix B of Two Answers on
Heavy-Ball Dynamics and are evaluated in exact rational arithmetic.
"""
from __future__ import annotations
import sympy as sp
from functools import lru_cache


from .schema import polynomial, rational, rational_string


@lru_cache(maxsize=2)
def model(include_checks=True):
    z, c, GG, UU = sp.symbols("zeta c G u")
    qm, qp, rm, rp = z*z-2*z+2, z*z+2*z+2, z*z-2, z*z+2
    em, ep = z*z-2*z-2, z*z+2*z-2
    K6 = z**6-4*z**5+4*z**4+8*z*z-16*z+8
    F8 = 15*z**8-92*z**7+224*z**6-440*z**5+760*z**4-880*z**3+896*z*z-736*z+240
    M10 = 5*z**10-44*z**9+170*z**8-368*z**7+744*z**6-1376*z**5+1488*z**4-1472*z**3+1360*z*z-704*z+160
    D14 = 5*z**14-34*z**13+42*z**12+648*z**11-3460*z**10+8296*z**9-14984*z**8+23616*z**7-29968*z**6+33184*z**5-27680*z**4+10368*z**3+1344*z*z-2176*z+640
    N10 = 5*z**10-24*z**9+74*z**8-512*z**7+1448*z**6-2240*z**5+2896*z**4-2048*z**3+592*z*z-384*z+160
    N8 = 5*z**8-24*z**7+48*z**6-104*z**5+184*z**4-208*z**3+192*z*z-192*z+80
    N12 = 25*z**12-314*z**11+1764*z**10-6092*z**9+14988*z**8-28736*z**7+44832*z**6-57472*z**5+59952*z**4-48736*z**3+28224*z*z-10048*z+1600
    f1 = z**3-z*z-2
    G = (z**4+4)/(8*z*rm)
    u = qm**2/(z**4-4)
    W = qm**2*qp*(7*z*z-18*z+14)/(8*rp*K6)
    a = qm**3/(2*z*rm*rp)
    b = -2*z*(3*z**4-10*z**3+16*z*z-20*z+12)/(rm**2*rp)
    mc = 4*z*z*F8/(rm*M10)
    d = qm**3*D14/(rm**3*rp**2*M10)
    gap = 1-u*u+a*mc+b
    slope = 32*z*z*qm*(z**4-2*z**3-4*z+4)/(rp**3*em*ep)
    Ha = 162529280000*GG**12-238685519872*GG**10+77668708352*GG**8-6246545408*GG**6-58821872*GG**4+12933112*GG**2+229441
    P2 = 256*GG**4*(UU*UU-1)-512*GG**3*UU**3+768*GG**3*UU-32*GG**2*UU**4-480*GG**2*UU*UU-16*GG*UU**3-UU**4-16*UU*UU
    if not include_checks:
        return locals()
    T, U = sp.chebyshevt, sp.chebyshevu
    moments = [sp.S.One, mc]
    for n in range(10):
        moments.append(sp.cancel(-a*moments[-1]-b*moments[-2]))
    def integrate(p):
        p = sp.Poly(sp.expand(p), c)
        answer=sp.S.Zero
        for e,co in p.terms():
            co=sp.cancel(co.subs({GG:G,UU:u}))
            answer=sp.cancel(answer+co*moments[e[0]])
        return answer
    slacks = {}
    for n in range(1,10):
        for sign in (-1,1):
            # Fixed source moments; cancel only after summing the finite polynomial.
            av = integrate((1-c*c-UU*UU)*(T(n,GG)-T(n,c))+sign*2*UU*(1-c*c)*U(n-1,c))
            slacks[f"{'lower' if sign<0 else 'upper'}{n}"] = sp.cancel(av-sign*d*U(n-1,G))
    signs = {
        "G_lower":G-sp.Rational(10233,10000), "G_upper":sp.Rational(10337,10000)-G,
        "u_lower":u-sp.Rational(511,1000), "u_upper":sp.Rational(517,1000)-u,
        "W_lower":W-sp.Rational(181,500), "W_upper":sp.Rational(183,500)-W,
        "b_negative":-b, "midpoint":-mc-a/2,
        "mean_root_relation":sp.cancel(-(mc*mc+a*mc+b)/f1),
        "d_positive":d, "gap_lower":gap-sp.Rational(7,25),
        "gap_square":(gap-sp.Rational(7,25))**2*(G*G-1)-d*d,
        "tail_gap":sp.Rational(21,20)-gap-2*u*u,
        "slope_positive":slope, "slope_lt_one":1-slope,
        "G_decreasing":-sp.diff(G,z), "N12_decreasing":-sp.diff(N12,z),
        "root_minus_outer":sp.Rational(-101,200)**2+a*sp.Rational(-101,200)+b,
        "root_minus_inner":-(sp.Rational(-12,25)**2+a*sp.Rational(-12,25)+b),
        "root_plus_inner":-(sp.Rational(1,4)**2+a*sp.Rational(1,4)+b),
        "root_plus_outer":sp.Rational(57,200)**2+a*sp.Rational(57,200)+b,
        **{name:value for name,value in slacks.items() if name not in ("lower1","upper2","upper3","upper5")},
        "upper5_factor":sp.cancel(slacks["upper5"]/N12),
    }
    identities = {
        "curve":P2.subs({GG:G,UU:u}),
        "K6_sum_squares":K6-z**4*(z-2)**2-8*(z-1)**2,
        "upper_weight":1-W-em**2*ep**2/(8*rp*K6),
        "u_ratio":u/G-8*z*qm/(rp*qp),
        "gap_formula":gap-8*z*qm**4*N8/(rm**2*rp**2*M10),
        "mean_root_formula":mc*mc+a*mc+b-32*z**3*em*ep*(z**3+2*z-4)*f1*N10/(rm**2*rp*M10**2),
        "slope":sp.diff(u,z)-slope*sp.diff(G,z),
        "touching_spiral":u-1+1/(2*G)-8*f1**2/(rm*rp*qm*qp),
        **{name:slacks[name] for name in ("lower1","upper2","upper3")},
    }
    M=8*G**3+4*G**2*c+4*G*c*c-4*G-W*(4*G*c*c-2*G+c)
    N=4*G*G+4*G*c-W*(4*G*c+1)
    identities["dual_square"] = sp.Poly(sp.cancel(-((1-c*c-u*u)*M-2*u*(1-c*c)*N)-4*G*(1-W)*(c*c+a*c+b)**2),c)
    ha_num, ha_den = sp.fraction(sp.cancel(Ha.subs(GG,G)))
    ha_quotient, ha_remainder = sp.div(sp.Poly(ha_num,z),sp.Poly(N12,z))
    assert ha_remainder.is_zero
    return locals()


def taylor_dominance(poly,z):
    a,delta=sp.Rational(6789,4000),sp.Rational(7,4000)
    coeffs=sp.Poly(sp.expand(poly.subs(z,z+a)),z).all_coeffs()[::-1]
    budget=sum(abs(k)*delta**i for i,k in enumerate(coeffs) if i)
    return coeffs[0],budget


def export():
    m=model(); z=m["z"]
    polys={name:m[name] for name in ("qm","qp","rm","rp","em","ep","K6","F8","M10","D14","N10","N8","N12","f1")}
    polys["Ha"]=m["Ha"]
    factors={}
    checks=[]
    # Exact endpoint proposals are independent of any floating-point root finder.
    zl,zu=sp.Rational(16989316152,10**10),sp.Rational(16989316153,10**10)
    gl,gu=sp.Rational(51179,50000),sp.Rational(102359,100000)
    switch=32*m["GG"]**3-36*m["GG"]**2+4*m["GG"]-1
    endpoint_checks={
        "zeta1_bracket":m["f1"].subs(z,sp.Rational(4239,2500))<0<m["f1"].subs(z,sp.Rational(16957,10000)),
        "zetaA_fine_bracket":m["N12"].subs(z,zl)>0>m["N12"].subs(z,zu),
        "Ga_bracket":m["Ha"].subs(m["GG"],gl)<0<m["Ha"].subs(m["GG"],gu),
        "Ga_parameter_image":gl<m["G"].subs(z,zu) and m["G"].subs(z,zl)<gu,
        "G1_bracket":switch.subs(m["GG"],sp.Rational(103329,100000))<0<switch.subs(m["GG"],sp.Rational(10333,10000)),
    }
    for name,passed in endpoint_checks.items():
        assert bool(passed),name
        checks.append({"id":name,"kind":"exact_endpoint_signs","passed":True})
    for name,expr in m["identities"].items():
        good=expr.is_zero if isinstance(expr,sp.Poly) else sp.cancel(expr)==0
        assert good,name
        checks.append({"id":name,"kind":"exact_identity","passed":True})
    for name,expr in m["signs"].items():
        n,d=sp.fraction(sp.factor(sp.cancel(expr)))
        sign=1
        for side in (n,d):
            const,fac=sp.factor_list(side,z)
            sign*=sp.sign(const)
            for poly,power in fac:
                key=sp.srepr(poly)
                if key not in factors:
                    val,budget=taylor_dominance(poly,z)
                    assert abs(val)>budget,(name,poly)
                    factors[key]=(poly,val,budget)
                sign*=sp.sign(factors[key][1])**power
        assert sign==1,name
        checks.append({"id":name,"kind":"rational_positive","passed":True})
    for i,(poly,val,budget) in enumerate(factors.values()):
        polys[f"sign_factor_{i}"]=poly
        checks.append({"id":f"taylor_{i}","kind":"taylor_dominance","passed":True,
                       "center_value":rational_string(val),"variation_bound":rational_string(budget)})
    rats={name:m[name] for name in ("G","u","W","a","b","mc","d","gap","slope")}
    rats.update(m["slacks"]); rats.update(m["signs"])
    return {"id":"p2-rational","variables":["zeta"],
            "polynomials":{name:polynomial(p,[m["GG"]] if name=="Ha" else [z]) for name,p in polys.items()},
            "rationals":{name:rational(p,[z]) for name,p in rats.items()},
            "intervals":{"J":["3391/2000","1699/1000"],"zeta1":["4239/2500","16957/10000"],
                         "zetaA":["16989/10000","1699/1000"],
                         "zetaA_fine":["2123664519/1250000000","16989316153/10000000000"],
                         "Ga":["51179/50000","102359/100000"],
                         "G1":["103329/100000","10333/10000"]},
            "checks":checks}
