import polyak.Numerics.Root

/-!
Article: Appendix B, Theorem p5h0, the critical P₅ algebraic parameter.
Use: the root is isolated with exact rational endpoints and a checked derivative
sign on the whole interval.  Its equation is the source quintic, independently
of the executable coefficient representation.
-/

noncomputable section
open scoped Polynomial
namespace polyak.Boundary.P5
open Polynomial Numerics LeanCert.Core LeanCert.Engine

/-- Article: q₅, the consistency polynomial of the three critical dual equations. -/
def criticalPolynomial : ℚ[X] := C 32*X^5-C 40*X^4+C 16*X^3-C 6*X^2-C 12*X+C 3

/-- Article: the exact critical root interval (0.23188,0.23189). -/
def criticalInterval : IntervalRat := ⟨5797/25000,23189/100000,by norm_num⟩

/-- Article: the negative quintic derivative, encoded independently of its source. -/
def criticalNegativeDerivativeCode : PolynomialCode (-criticalPolynomial.derivative) where
  code := ⟨#[12,12,-48,160,-160]⟩
  exact := by
    change C 12+X*(C 12+X*(C (-48)+X*(C 160+X*(C (-160)+X*0)))) =
      -(C 32*X^5-C 40*X^4+C 16*X^3-C 6*X^2-C 12*X+C 3 : ℚ[X]).derivative
    simp
    norm_num
    simp only [Polynomial.C_ofNat]
    ring

/-- Article: q₅ is strictly decreasing throughout the whole root interval. -/
theorem critical_derivative_negative :
    ∀ x ∈ criticalInterval, Polynomial.aeval x criticalPolynomial.derivative < 0 := by
  have hc : QPoly.bernsteinCheck .strictLower criticalNegativeDerivativeCode.code 0 criticalInterval 0 = true := by
    change QPoly.bernsteinCheck .strictLower ⟨#[12,12,-48,160,-160]⟩ 0
      ⟨5797/25000,23189/100000,by norm_num⟩ 0 = true
    decide +kernel
  intro x hx
  have hp := criticalNegativeDerivativeCode.positive criticalInterval 0 hc x hx
  simpa only [map_neg,neg_pos] using hp

/-- Article: exact opposite endpoint signs of q₅. -/
theorem critical_endpoint_signs :
    0 < Polynomial.aeval (criticalInterval.lo : ℝ) criticalPolynomial ∧
      Polynomial.aeval (criticalInterval.hi : ℝ) criticalPolynomial < 0 := by
  norm_num [criticalInterval,criticalPolynomial]

/-- Article: existence and uniqueness of the source critical root in its exact enclosure. -/
theorem critical_root_exists : Nonempty (IsolatedRoot criticalPolynomial criticalInterval) := by
  obtain ⟨r⟩ := exists_isolatedRoot (p := -criticalPolynomial) criticalInterval
    (by simpa only [map_neg,neg_lt_zero] using critical_endpoint_signs.1)
    (by simpa only [map_neg,neg_pos] using critical_endpoint_signs.2)
    (by intro x hx; simpa only [derivative_neg,map_neg,neg_pos] using critical_derivative_negative x hx)
  refine ⟨⟨r.value,r.mem,?_,?_⟩⟩
  · simpa only [map_neg,neg_eq_zero] using r.root
  · intro x hx hr
    exact r.unique x hx (by simpa only [map_neg,neg_eq_zero] using hr)

/-- Article: y₀, selected from a proved isolated-root specification. -/
def criticalRoot : IsolatedRoot criticalPolynomial criticalInterval := Classical.choice critical_root_exists

/-- Article: the actual critical frequency cosine. -/
def y₀ : ℝ := criticalRoot.value

/-- Article: exact equation, in ordinary real polynomial notation. -/
theorem y₀_equation : 32*y₀^5-40*y₀^4+16*y₀^3-6*y₀^2-12*y₀+3 = 0 := by
  have h := criticalRoot.root
  simpa [criticalPolynomial,y₀] using h

/-- Article: strict root enclosure, with the printed decimal endpoints treated as rationals. -/
theorem y₀_bounds : (5797/25000 : ℝ) < y₀ ∧ y₀ < 23189/100000 := by
  have hm := criticalRoot.mem
  rw [IntervalRat.mem_def] at hm
  norm_num [criticalInterval] at hm
  change (5797/25000 : ℝ) ≤ y₀ ∧ y₀ ≤ 23189/100000 at hm
  constructor
  · apply lt_of_le_of_ne hm.1
    intro he
    have hz := y₀_equation
    rw [← he] at hz
    norm_num at hz
  · apply lt_of_le_of_ne hm.2
    intro he
    have hz := y₀_equation
    rw [he] at hz
    norm_num at hz

/-- Article: the critical auxiliary atom is strictly inside the frequency interval. -/
theorem y₀_interior : -1 < y₀ ∧ y₀ < 1 := by
  have h := y₀_bounds
  constructor <;> linarith [h.1,h.2]

end polyak.Boundary.P5
