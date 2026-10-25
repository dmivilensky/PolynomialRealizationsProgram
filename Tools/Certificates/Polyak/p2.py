"""Read the finite P2 source data needed by the local Lean templates.

No upstream Python module runs here.  The base polynomial coefficients and
rational annotations come from Payload; the rational source constructions
below mirror the independently defined Lean formulas.  Their agreement with
the archive is an operational consistency check, not a mathematical axiom.
"""
import sympy as sp

from .Payload import group, polynomial, rational


def model(include_checks=False):
    """Supply only the small source model used by the P2 Lean builders."""
    if include_checks is not False:
        raise ValueError("the Lean consumer does not run the producer's P2 checks")
    data = group("p2")
    z, c, GG, UU = sp.symbols("zeta c G u")

    def base(name, variables=("zeta",)):
        record = data["polynomials"][name]
        if record["variables"] != list(variables):
            raise ValueError("unexpected P2 polynomial variable order: " + name)
        return polynomial(record)

    qm, qp, rm, rp, em, ep = [base(name) for name in
                               ("qm", "qp", "rm", "rp", "em", "ep")]
    K6, F8, M10, D14, N10, N8, N12, f1 = [base(name) for name in
        ("K6", "F8", "M10", "D14", "N10", "N8", "N12", "f1")]
    Ha = base("Ha", ("G",))
    G = (z**4+4)/(8*z*rm)
    u = qm**2/(z**4-4)
    W = qm**2*qp*(7*z*z-18*z+14)/(8*rp*K6)
    a = qm**3/(2*z*rm*rp)
    b = -2*z*(3*z**4-10*z**3+16*z*z-20*z+12)/(rm**2*rp)
    mc = 4*z*z*F8/(rm*M10)
    d = qm**3*D14/(rm**3*rp**2*M10)
    gap = 1-u*u+a*mc+b
    slope = 32*z*z*qm*(z**4-2*z**3-4*z+4)/(rp**3*em*ep)
    result = {"z": z, "c": c, "GG": GG, "UU": UU,
              "qm": qm, "qp": qp, "rm": rm, "rp": rp,
              "em": em, "ep": ep, "K6": K6, "F8": F8,
              "M10": M10, "D14": D14, "N10": N10, "N8": N8,
              "N12": N12, "f1": f1, "Ha": Ha,
              "G": G, "u": u, "W": W, "a": a, "b": b,
              "mc": mc, "d": d, "gap": gap, "slope": slope}
    for name in ("G", "u", "W", "a", "b", "mc", "d", "gap", "slope"):
        record = data["rationals"][name]
        if (record["numerator"]["variables"] != ["zeta"] or
                record["denominator"]["variables"] != ["zeta"]):
            raise ValueError("unexpected P2 rational variable order: " + name)
        if sp.cancel(result[name] - rational(record)) != 0:
            raise ValueError("P2 source differs from archived rational: " + name)
    return result
