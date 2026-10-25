"""Canonical exact interchange format, independent of SymPy expression printing.

Every rational is a reduced string with positive denominator. Polynomial terms
are nonzero and sorted by their exponent tuple, in the declared variable order.
Decimals, numerical roots and proposed interval boxes are never exact numbers.
"""
from fractions import Fraction

SCHEMA = "heavy-ball-part1-proof-v1"


def rational_string(value):
    q = Fraction(str(value))
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def polynomial(expr, variables):
    import sympy as s
    variables = tuple(variables)
    if s.sympify(expr).has(s.Float):
        raise ValueError("floating point values cannot define an exact source polynomial")
    p = s.Poly(expr, *variables, domain=s.QQ)
    return {"variables": [str(v) for v in variables],
            "terms": [[rational_string(c), list(m)]
                      for m, c in sorted(p.terms()) if c != 0]}


def rational(expr, variables):
    import sympy as s
    n, d = s.fraction(s.cancel(expr))
    return {"numerator": polynomial(n, variables),
            "denominator": polynomial(d, variables)}


def decode_polynomial(data):
    import sympy as s
    variables = tuple(s.Symbol(v) for v in data["variables"])
    expr = sum(s.Rational(q) * s.prod(v**e for v, e in zip(variables, powers))
               for q, powers in data["terms"])
    return expr, variables


def validate_polynomial(data):
    names = data["variables"]
    if any(not isinstance(name,str) or not name for name in names) or len(set(names)) != len(names):
        raise ValueError("duplicate polynomial variable")
    previous = None
    for coefficient, powers in data["terms"]:
        if rational_string(coefficient) != coefficient or Fraction(coefficient) == 0:
            raise ValueError("noncanonical or zero coefficient")
        if len(powers) != len(names) or any(type(e) is not int or e < 0 for e in powers):
            raise ValueError("invalid polynomial exponents")
        if previous is not None and tuple(powers) <= previous:
            raise ValueError("polynomial terms are not strictly ordered")
        previous = tuple(powers)


def validate(data):
    """Check every nested polynomial and canonical rational interval."""
    if isinstance(data, dict):
        if set(data) == {"variables", "terms"}:
            validate_polynomial(data)
        else:
            intervals = list(data.get("intervals",{}).values())
            intervals += [data[key] for key in ("interval","q_interval") if key in data]
            for interval in intervals:
                if len(interval) != 2 or any(rational_string(q) != q for q in interval) or Fraction(interval[0]) > Fraction(interval[1]):
                    raise ValueError("noncanonical or reversed rational interval")
            for check in data.get("checks",[]):
                # Some groups carry a source inequality and its witness tree,
                # without making a Python verdict part of that data record.
                if "passed" in check and check["passed"] is not True:
                    raise ValueError("an exported external check failed")
            for value in data.values():
                validate(value)
    elif isinstance(data, list):
        for value in data:
            validate(value)
