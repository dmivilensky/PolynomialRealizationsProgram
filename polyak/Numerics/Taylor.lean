import polyak.Numerics.Polynomial

/-!
Article: Appendix B, Lemma p2certs, Taylor-dominance sign checks.
Use: exact rational finite data certify a polynomial sign on an entire interval.
Proof: the exact shifted polynomial expansion and the finite triangle inequality;
there is no floating-point estimate or unproved Taylor remainder.
-/

noncomputable section
open scoped BigOperators Polynomial
namespace polyak.Numerics
open LeanCert.Core LeanCert.Engine

/-- Article: exact interval used only to obtain coefficients of p(a+X). -/
def taylorShiftInterval (a : ℚ) : IntervalRat := ⟨a,a+1,by linarith⟩

/-- Article: finite rational coefficients of the exact shifted source p(a+X), padded to be nonempty. -/
def taylorCoeffs (p : QPoly) (a : ℚ) : List ℚ := QPoly.shiftedCoeffs p (taylorShiftInterval a)

/-- Article: the finite nonconstant Taylor coefficient index set. -/
def taylorIndices (p : QPoly) (a : ℚ) : Finset ℕ := (Finset.range (taylorCoeffs p a).length).erase 0

/-- Article: exact rational bound for the total nonconstant Taylor variation. -/
def taylorBudget (p : QPoly) (a δ : ℚ) : ℚ :=
  ∑ k ∈ taylorIndices p a, |(taylorCoeffs p a).getD k 0| *δ^k

/-- Article: executable exact positive Taylor-dominance check. -/
def taylorPositiveCheck (p : QPoly) (a δ : ℚ) : Bool :=
  decide (0 ≤ δ ∧ taylorBudget p a δ < (taylorCoeffs p a).getD 0 0)

/-- Article: exact finite Taylor expansion about the rational center. -/
theorem taylor_expansion (p : QPoly) (a : ℚ) (x : ℝ) :
    Polynomial.aeval x p.toPoly = ((taylorCoeffs p a).getD 0 0 : ℝ)+
      ∑ k ∈ taylorIndices p a, ((taylorCoeffs p a).getD k 0 : ℝ)*(x-a)^k := by
  have h := QPoly.aeval_shiftedCoeffs p (taylorShiftInterval a) (x-a)
  have hpoint : (taylorShiftInterval a).lo +
      (((taylorShiftInterval a).hi : ℝ)-(taylorShiftInterval a).lo)*(x-a) = x := by
    simp [taylorShiftInterval]
  rw [hpoint] at h
  change Polynomial.aeval x p.toPoly = ∑ k ∈ Finset.range (taylorCoeffs p a).length,
    ((taylorCoeffs p a).getD k 0 : ℝ)*(x-a)^k at h
  have hzero : 0 ∈ Finset.range (taylorCoeffs p a).length :=
    Finset.mem_range.mpr (QPoly.shiftedCoeffs_length_pos p (taylorShiftInterval a))
  rw [← Finset.sum_erase_add _ _ hzero] at h
  simpa only [pow_zero,mul_one,taylorIndices,add_comm] using h

/-- Article: exact Taylor coefficient dominance bounds variation on the whole interval. -/
theorem taylor_variation_le (p : QPoly) (a δ : ℚ) (x : ℝ)
    (hx : |x-(a : ℝ)| ≤ δ) :
    |Polynomial.aeval x p.toPoly-((taylorCoeffs p a).getD 0 0 : ℝ)| ≤ (taylorBudget p a δ : ℝ) := by
  have he := taylor_expansion p a x
  rw [he,add_sub_cancel_left]
  calc
    _ ≤ ∑ k ∈ taylorIndices p a, |((taylorCoeffs p a).getD k 0 : ℝ)*(x-a)^k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ taylorIndices p a, |((taylorCoeffs p a).getD k 0 : ℝ)| *(δ : ℝ)^k := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx k) (abs_nonneg _)
    _ = _ := by simp [taylorBudget]

/-- Article: a successful Taylor-dominance check proves positivity of the specified polynomial source. -/
theorem PolynomialCode.positive_of_taylor {p : ℚ[X]} (P : PolynomialCode p) (a δ : ℚ)
    (hc : taylorPositiveCheck P.code a δ = true) :
    ∀ x : ℝ, |x-(a : ℝ)| ≤ δ → 0 < Polynomial.aeval x p := by
  have hh : 0 ≤ δ ∧ taylorBudget P.code a δ < (taylorCoeffs P.code a).getD 0 0 :=
    of_decide_eq_true hc
  intro x hx
  have h := taylor_variation_le P.code a δ x hx
  rw [P.exact] at h
  have hdom : (taylorBudget P.code a δ : ℝ) < ((taylorCoeffs P.code a).getD 0 0 : ℝ) := by
    exact_mod_cast hh.2
  linarith [abs_le.mp h |>.1]

end polyak.Numerics
