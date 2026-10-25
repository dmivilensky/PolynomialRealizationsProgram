"""Archived initialized-spiral sources and literal Lean witness rendering.

This consumer neither constructs branch witnesses nor imports their producer.
The finite source expressions, intervals and numerator_witness trees are read
only through the locally configured Payload.  Lean independently checks every
emitted mathematical identity and branch witness.
"""
from fractions import Fraction
from pathlib import Path

import sympy as s

from .Payload import group, polynomial, rational

RHO, Q = s.symbols("rho q")


def _coefficients(expr):
    p = s.Poly(expr, RHO, domain=s.QQ)
    return ([Fraction(p.nth(j)) for j in range(max(0, p.degree())+1)]
            if not p.is_zero else [Fraction(0)])


def integer_source(expr):
    numerator, _ = s.fraction(s.cancel(expr))
    p = s.Poly(numerator, Q)
    if p.is_zero:
        return [[0]]
    result = []
    for j in range(p.degree()+1):
        cs = _coefficients(p.nth(j))
        if any(c.denominator != 1 for c in cs):
            raise ValueError("numerator has a noninteger coefficient")
        result.append([c.numerator for c in cs])
    return result


def _source_names():
    names = []
    for label in ("lower", "upper"):
        names.extend((f"I.{label}.constant", f"I.{label}.norm",
                      f"II.{label}.beta", f"II.{label}.quadratic"))
        for residue in range(3):
            vertex = (label, residue) in {("lower", 0), ("lower", 1), ("upper", 2)}
            names.extend((f"II.{label}.{residue}.at_one",
                          f"II.{label}.{residue}.{'derivative' if vertex else 'discriminant'}"))
        names.extend((f"III.{label}.derivative", f"III.{label}.constant",
                      f"III.{label}.norm"))
    for k in range(1, 10):
        names.extend((f"III.k{k}.lower", f"III.k{k}.upper"))
    return names


def _records():
    records = group("startup")["checks"]
    if [record["name"] for record in records] != _source_names():
        raise ValueError("unexpected initialized-spiral source order or names")
    for record in records:
        expr = record["source"]
        if (expr["numerator"]["variables"] != ["rho", "q"] or
                expr["denominator"]["variables"] != ["rho", "q"]):
            raise ValueError("unexpected initialized-spiral variable order")
        if (record["witness_method"] != "integer-horner-physical-branch-v1" or
                record["witness_scale"] != "18446744073709551616"):
            raise ValueError("unsupported initialized-spiral witness method")
    return records


def source():
    """Read the 44 archived rational sources and exact closed intervals."""
    result = []
    for record in _records():
        bounds = [Fraction(value) for value in record["interval"]]
        if len(bounds) != 2 or bounds[0] > bounds[1]:
            raise ValueError("invalid initialized-spiral source interval")
        lo, hi = [s.Rational(value.numerator, value.denominator) for value in bounds]
        result.append((record["name"], s.cancel(rational(record["source"])), lo, hi))
    return tuple(result)


def _lean_rat(q):
    q=Fraction(q)
    return str(q.numerator) if q.denominator==1 else f"({q.numerator}/{q.denominator})"


def _lean_interval(lo,hi):
    return f"⟨{_lean_rat(lo)},{_lean_rat(hi)},by norm_num⟩"


def _lean_qpoly(expr):
    return "⟨#["+",".join(_lean_rat(x) for x in _coefficients(expr))+"]⟩"


def lean_numerator_modules(destination,only=None,integer=True):
    """Render the archived witness trees, without a witness search or fallback."""
    if integer is not True:
        raise ValueError("the archive supplies only integer physical-branch witnesses")
    destination=Path(destination)
    destination.mkdir(parents=True,exist_ok=True)
    paths=[]
    records=_records()
    for index,(name,expr,lo,hi) in enumerate(source()):
        if only is not None and index not in only:
            continue
        record=records[index]
        numerator,_=s.fraction(s.cancel(expr))
        archived_numerator=polynomial(record["source"]["numerator"])
        if s.expand(numerator-archived_numerator)!=0:
            raise ValueError("source numerator differs from canonical archived data: "+name)
        p=s.Poly(numerator,Q)
        code="["+",".join(_lean_qpoly(p.nth(j)) for j in range(p.degree()+1))+"]"
        tree=record["numerator_witness"]
        def lean_tree(w):
            if set(w)=={"q_interval"}:
                return ".leaf "+_lean_interval(*w["q_interval"])
            if set(w)!={"left","right"}:
                raise ValueError("invalid archived physical-branch witness node")
            return ".split ("+lean_tree(w["left"])+") ("+lean_tree(w["right"])+")"
        module=f"Check{index:02d}"
        source_data="["+",".join("["+",".join(str(c) for c in row)+"]" for row in integer_source(archived_numerator))+"]"
        text=f'''import polyak.Numerics.{"ComputedBivariate" if integer else "BivariateBranch"}

/-!
Article: initialized-spiral sign {name} on [{lo},{hi}].
Use: exact numerator coefficients and a closed physical-branch cover.
Proof: the stock Lean kernel checks all rational Bernstein and root-isolating signs.
-/

namespace polyak.Certificates.Startup.{module}
open LeanCert.Core LeanCert.Engine
open polyak.Numerics.BivariateBranch polyak.Numerics.ExecutableBranch

{f"/-- Article: exact integer numerator of the independently specified source sign. -/{chr(10)}def numeratorSource : polyak.Numerics.IntegerBivariate.Source := {source_data}{chr(10)}" if integer else ""}
/-- Article: exact numerator of the separately specified source sign. -/
def numerator : Code := {"polyak.Numerics.IntegerBivariate.rationalCode numeratorSource" if integer else code}

/-- Article: the source growth-factor interval, with both endpoints included. -/
def interval : IntervalRat := {_lean_interval(lo,hi)}

/-- Article: finite rational rectangles covering the whole physical branch. -/
def witness : Tree := {lean_tree(tree)}

/-- Article: acceptance is checked by the ordinary kernel, without native evaluation. -/
theorem accepted : {"polyak.Numerics.ComputedBivariate.check 18446744073709551616 numeratorSource" if integer else "check numerator"} interval witness=true := by decide +kernel

/-- Article: the actual source numerator is positive at every physical branch point. -/
theorem numerator_pos {{r q : ℝ}} (hrI : r∈interval) (hr : 0<r) (hq : 0<q)
    (hroot : polyak.Spiral.spiralPolynomial r q=0) : 0<value numerator r q :=
  {"polyak.Numerics.ComputedBivariate.check_sound" if integer else "check_sound"} witness accepted hrI hr hq hroot

end polyak.Certificates.Startup.{module}
'''
        path=destination/(module+".lean")
        path.write_text(text)
        paths.append(str(path))
    return paths
