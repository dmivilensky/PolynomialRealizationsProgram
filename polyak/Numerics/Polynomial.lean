import LeanCert.Engine.Algebra.QPolyBernstein
import chebyshev2.Numerics.IntegerExpression

/-!
Article: Appendix B, exact polynomial and rational sign certificates.
Use: keep the source polynomial separate from executable arrays and arithmetic-graph annotations.
Proof: every checker conclusion is transported through a proved source identity;
the interval and graph engines are existing kernel-checked libraries.
Source: LeanCert QPolyBernstein and chebyshev2 IntegerExpression.
-/

noncomputable section
open scoped Polynomial
namespace polyak.Numerics
open LeanCert.Core LeanCert.Engine

/-- Article: a rational polynomial source and its finite executable coefficient representation.
Use: a successful checker is always linked to the specified mathematical polynomial. -/
structure PolynomialCode (source : ℚ[X]) where
  /-- Article: finite exact rational coefficients. -/
  code : QPoly
  /-- Article: the source identity is checked independently of interval annotations. -/
  exact : code.toPoly = source

/-- Article: Bernstein certificates yield a real lower bound on the actual source polynomial. -/
theorem PolynomialCode.positive {p : ℚ[X]} (P : PolynomialCode p)
    (I : IntervalRat) (depth : ℕ)
    (hc : QPoly.bernsteinCheck .strictLower P.code 0 I depth = true) :
    ∀ x ∈ I, 0 < Polynomial.aeval x p := by
  intro x hx
  have h := QPoly.lt_aeval_of_bernsteinCheck hc x hx
  simpa only [P.exact,Rat.cast_zero] using h

/-- Article: Bernstein certificates also supply non-strict source bounds, preserving exact endpoints. -/
theorem PolynomialCode.lower {p : ℚ[X]} (P : PolynomialCode p)
    (I : IntervalRat) (bound : ℚ) (depth : ℕ)
    (hc : QPoly.bernsteinCheck .lower P.code bound I depth = true) :
    ∀ x ∈ I, (bound : ℝ) ≤ Polynomial.aeval x p := by
  simpa only [P.exact] using QPoly.le_aeval_of_bernsteinCheck hc

/-- Article: a rational function retains independent numerator and denominator sources. -/
structure RationalSource where
  /-- Article: mathematical numerator. -/
  numerator : ℚ[X]
  /-- Article: mathematical denominator. -/
  denominator : ℚ[X]

/-- Article: real evaluation of a rational source. No nonzero denominator is hidden in the type. -/
def RationalSource.value (r : RationalSource) (x : ℝ) : ℝ :=
  Polynomial.aeval x r.numerator / Polynomial.aeval x r.denominator

/-- Article: a certified positive denominator is nonzero throughout its interval. -/
theorem denominator_ne_zero_of_positive {p : ℚ[X]} (P : PolynomialCode p)
    (I : IntervalRat) (depth : ℕ)
    (hc : QPoly.bernsteinCheck .strictLower P.code 0 I depth = true)
    (x : ℝ) (hx : x ∈ I) : Polynomial.aeval x p ≠ 0 := (P.positive I depth hc x hx).ne'

/-- Article: division sign is certified only after a proved denominator sign. -/
theorem RationalSource.positive {r : RationalSource} {x : ℝ}
    (hn : 0 < Polynomial.aeval x r.numerator) (hd : 0 < Polynomial.aeval x r.denominator) :
    0 < r.value x := div_pos hn hd

/-- Article: exact rational interval boxes for a finite list of variables. -/
abbrev RationalBox (d : ℕ) := Fin d → IntervalRat

/-- Article: a real point belongs to an exact rational box coordinatewise. -/
def RationalBox.Contains {d : ℕ} (box : RationalBox d) (x : Fin d → ℝ) : Prop :=
  ∀ i, x i ∈ box i

open chebyshev2.Numerics.IntegerCertificate

/-- Article: the annotated arithmetic graph certifies the independently specified source value.
Use: graph annotations cannot silently redefine the formula whose sign is being proved. -/
theorem graph_source_enclosed {s : ℕ} (hs : 0 < s) (nodes : List Node)
    {stack : List Bounds} {v : ℕ → ℝ} (hv : Encloses s stack v)
    (hc : programCheck s stack nodes = true) {i : ℕ} {source : chebyshev2.Numerics.IntegerCertificate.Expr}
    (he : expressionCheck nodes i source = true) {I : Bounds}
    (hi : (programBounds stack nodes)[i]? = some I) {actual : ℝ}
    (hsource : source.value v = actual) : I.Mem s actual := by
  rw [← hsource]
  exact source_enclosed hs nodes hv hc he hi

end polyak.Numerics
