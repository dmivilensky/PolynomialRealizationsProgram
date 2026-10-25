import polyak.Numerics.Polynomial

/-!
Article: Appendix B, identities modulo an algebraic defining polynomial.
Use: reduce large exact polynomial and rational identities at a specified root.
Proof: evaluate a checked polynomial identity; each required denominator is
separately proved nonzero rather than entrusted to a symbolic simplifier.
-/

noncomputable section
open scoped Polynomial
namespace polyak.Numerics
open LeanCert.Engine

/-- Article: executable modular identity on finite exact coefficient arrays.
Use: the source polynomials remain independent semantic objects. -/
def remainderCodeCheck (p defining quotient remainder : QPoly) : Bool :=
  decide (p.trim = ((defining.mul quotient).add remainder).trim)

/-- Article: a checked finite-array modular identity entails the actual source-polynomial identity. -/
theorem remainderCodeCheck_sound {p defining quotient remainder : QPoly}
    (hc : remainderCodeCheck p defining quotient remainder = true) :
    p.toPoly=defining.toPoly*quotient.toPoly+remainder.toPoly := by
  have h : p.trim=((defining.mul quotient).add remainder).trim := of_decide_eq_true hc
  have he := congrArg QPoly.toPoly h
  simpa only [QPoly.toPoly_trim,QPoly.toPoly_add,QPoly.toPoly_mul] using he

/-- Article: executable modular computation gives an exact theorem at every source algebraic root. -/
theorem eval_at_root_of_code {p defining quotient remainder : QPoly}
    (hc : remainderCodeCheck p defining quotient remainder = true)
    {x : ℝ} (hx : Polynomial.aeval x defining.toPoly=0) :
    Polynomial.aeval x p.toPoly=Polynomial.aeval x remainder.toPoly := by
  rw [remainderCodeCheck_sound hc,map_add,map_mul,hx,zero_mul,zero_add]

/-- Article: exact polynomial identity modulo the defining polynomial.
Use: finite coefficient equality is an executable, kernel-checked certificate. -/
def remainderIdentityCheck (p defining quotient remainder : ℚ[X]) : Bool :=
  decide (p = defining*quotient+remainder)

/-- Article: successful modular identity certifies the actual polynomial at every root. -/
theorem eval_at_root_of_remainder {p defining quotient remainder : ℚ[X]}
    (hc : remainderIdentityCheck p defining quotient remainder = true)
    {x : ℝ} (hx : Polynomial.aeval x defining = 0) :
    Polynomial.aeval x p = Polynomial.aeval x remainder := by
  have h : p=defining*quotient+remainder := of_decide_eq_true hc
  rw [h,map_add,map_mul,hx,zero_mul,zero_add]

/-- Article: clearing rational denominators is valid at an algebraic root only with nonzero proofs. -/
theorem rational_eq_at_root {p q r s defining quotient : ℚ[X]}
    (hc : remainderIdentityCheck (p*s-r*q) defining quotient 0 = true)
    {x : ℝ} (hx : Polynomial.aeval x defining=0)
    (hq : Polynomial.aeval x q ≠ 0) (hs : Polynomial.aeval x s ≠ 0) :
    Polynomial.aeval x p/Polynomial.aeval x q = Polynomial.aeval x r/Polynomial.aeval x s := by
  have h := eval_at_root_of_remainder hc hx
  simp only [map_sub,map_mul,map_zero] at h
  apply (div_eq_div_iff hq hs).mpr
  linarith

/-- Article: a polynomial identity without a root hypothesis is the zero-modulus special case. -/
theorem polynomial_eq_of_coefficient_check {p q : ℚ[X]} (hc : decide (p=q)=true) :
    ∀ x : ℝ, Polynomial.aeval x p=Polynomial.aeval x q := by
  rw [of_decide_eq_true hc]
  intro x
  rfl

end polyak.Numerics
