import polyak.Dynamics.Tuning
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: (spiralpoly), Appendix B following Proposition spiral.
Use: the unique positive spiral factor and its exact threshold, independently
of the later classification of optimal spectra.
Proof: a strictly increasing polynomial on [q,∞), a negative sign below q,
and the intermediate value theorem; all derivatives are exact polynomials.
-/

noncomputable section

open scoped goldenRatio

namespace polyak.Spiral

/-- Article: F(ρ,q) in (spiralpoly). -/
def spiralPolynomial (ρ q : ℝ) : ℝ :=
  ρ^2*(ρ^2+1)-2*q*ρ*(ρ^2-ρ+1)-q^2*(ρ^2+1)

/-- Article: useful positive-root factorization. -/
theorem spiralPolynomial_rewrite (ρ q : ℝ) :
    spiralPolynomial ρ q = (ρ-q)^2*(ρ^2+1)-2*q^2+2*q*(1-q)*ρ^2 := by
  unfold spiralPolynomial
  ring

/-- Article: exact derivative with respect to the growth factor. -/
def spiralDerivative (ρ q : ℝ) : ℝ :=
  2*(ρ-q)*(ρ^2+1)+2*ρ*(ρ-q)^2+4*q*(1-q)*ρ

/-- Article: exact derivative with respect to q. -/
def spiralParameterDerivative (ρ q : ℝ) : ℝ :=
  -2*ρ*(ρ^2-ρ+1)-2*q*(ρ^2+1)

/-- Article: polynomial regularity in the growth factor. -/
theorem hasDerivAt_spiralPolynomial (ρ q : ℝ) :
    HasDerivAt (fun r => spiralPolynomial r q) (spiralDerivative ρ q) ρ := by
  have h := (((hasDerivAt_id ρ).sub_const q).pow 2).mul
    (((hasDerivAt_id ρ).pow 2).add_const 1)
  have h' := h.sub_const (2*q^2)
  have h'' := h'.add (((hasDerivAt_id ρ).pow 2).const_mul (2*q*(1-q)))
  convert h'' using 1
  · funext r
    simp only [spiralPolynomial_rewrite, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, show (2-1 : ℕ) = 1 from rfl, pow_one,
      mul_one, spiralDerivative]
    ring

/-- Article: polynomial regularity in the condition parameter. -/
theorem hasDerivAt_spiralPolynomial_parameter (ρ q : ℝ) :
    HasDerivAt (fun s => spiralPolynomial ρ s) (spiralParameterDerivative ρ q) q := by
  have h := ((hasDerivAt_const q (ρ^2*(ρ^2+1))).sub
    ((hasDerivAt_id q).const_mul (2*ρ*(ρ^2-ρ+1)))).sub
      (((hasDerivAt_id q).pow 2).mul_const (ρ^2+1))
  convert h using 1
  · funext s
    simp only [spiralPolynomial, Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [spiralParameterDerivative, id_eq, Nat.cast_ofNat,
      show (2-1 : ℕ) = 1 from rfl, pow_one, mul_one]
    ring

/-- Article: Fρ>0 on the entire interval where a positive root can occur. -/
theorem spiralDerivative_pos {ρ q : ℝ} (hq : 0 < q) (hq1 : q < 1) (hρ : q ≤ ρ) :
    0 < spiralDerivative ρ q := by
  have hρ0 : 0 < ρ := hq.trans_le hρ
  unfold spiralDerivative
  have h₁ : 0 ≤ 2*(ρ-q)*(ρ^2+1) := by positivity
  have h₂ : 0 ≤ 2*ρ*(ρ-q)^2 := by positivity
  have h₃ : 0 < 4*q*(1-q)*ρ := by positivity
  linarith

/-- Article: Fq<0 for every positive q and ρ. -/
theorem spiralParameterDerivative_neg {ρ q : ℝ} (hρ : 0 < ρ) (hq : 0 < q) :
    spiralParameterDerivative ρ q < 0 := by
  have hs : 0 < ρ^2-ρ+1 := by nlinarith [sq_nonneg (ρ-1/2)]
  unfold spiralParameterDerivative
  have h₁ : 0 < 2*ρ*(ρ^2-ρ+1) := by positivity
  have h₂ : 0 < 2*q*(ρ^2+1) := by positivity
  linarith

/-- Article: F is strictly increasing beyond q. -/
theorem spiralPolynomial_strictMonoOn {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    StrictMonoOn (fun ρ => spiralPolynomial ρ q) (Set.Ici q) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici q)
  · exact (by unfold spiralPolynomial; fun_prop : Continuous (fun ρ => spiralPolynomial ρ q)).continuousOn
  · intro ρ hρ
    rw [(hasDerivAt_spiralPolynomial ρ q).deriv]
    exact spiralDerivative_pos hq hq1 (by have := interior_subset hρ; exact this)

/-- Article: no positive root is at or below q. Proof: both displayed terms have the negative sign. -/
theorem spiralPolynomial_neg_of_le {ρ q : ℝ} (hρ : 0 < ρ) (hq : ρ ≤ q) :
    spiralPolynomial ρ q < 0 := by
  have hq0 : 0 < q := hρ.trans_le hq
  have hs : 0 < ρ^2-ρ+1 := by nlinarith [sq_nonneg (ρ-1/2)]
  have hsq : ρ^2-q^2 ≤ 0 := by nlinarith
  have h₁ := mul_nonpos_of_nonpos_of_nonneg hsq (show 0 ≤ ρ^2+1 by positivity)
  have h₂ : 0 < 2*q*ρ*(ρ^2-ρ+1) := by positivity
  unfold spiralPolynomial
  nlinarith [h₁, h₂]

/-- Article: an explicit finite positive endpoint for the root-existence argument. -/
theorem spiralPolynomial_three_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    0 < spiralPolynomial 3 q := by
  have hq2 : q^2 < 1 := by nlinarith
  unfold spiralPolynomial
  norm_num
  nlinarith

/-- Article: existence and uniqueness of the positive spiral factor. -/
theorem existsUnique_spiral_root {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃! ρ : ℝ, 0 < ρ ∧ spiralPolynomial ρ q = 0 := by
  have hqneg := spiralPolynomial_neg_of_le hq le_rfl
  have h3pos := spiralPolynomial_three_pos hq hq1
  have hcont : ContinuousOn (fun ρ => spiralPolynomial ρ q) (Set.Icc q 3) :=
    (by unfold spiralPolynomial; fun_prop : Continuous (fun ρ => spiralPolynomial ρ q)).continuousOn
  obtain ⟨ρ,hρ,hroot⟩ := intermediate_value_Icc (by linarith : q ≤ 3) hcont
    (show (0 : ℝ) ∈ Set.Icc (spiralPolynomial q q) (spiralPolynomial 3 q) from ⟨hqneg.le,h3pos.le⟩)
  refine ⟨ρ,⟨hq.trans_le hρ.1,hroot⟩,fun y hy => ?_⟩
  have hyq : q < y := by
    by_contra hh
    have hn := spiralPolynomial_neg_of_le hy.1 (le_of_not_gt hh)
    rw [hy.2] at hn
    linarith
  exact (spiralPolynomial_strictMonoOn hq hq1).injOn (Set.mem_Ici.mpr hyq.le) hρ.1
    (hy.2.trans hroot.symm)

/-- Article: ρ_sp, totalized outside the source parameter interval only for convenient notation. -/
def factor (q : ℝ) : ℝ := if h : 0 < q ∧ q < 1 then
  Classical.choose (existsUnique_spiral_root h.1 h.2) else 1

/-- Article: the selected spiral factor is positive and satisfies the original quartic. -/
theorem factor_spec {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    0 < factor q ∧ spiralPolynomial (factor q) q = 0 := by
  unfold factor
  split_ifs with h
  · exact (Classical.choose_spec (existsUnique_spiral_root h.1 h.2)).1
  · exact (h ⟨hq,hq1⟩).elim

/-- Article: the nonlinear spiral factor strictly exceeds the quadratic factor. -/
theorem q_lt_factor {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : q < factor q := by
  have hs := factor_spec hq hq1
  by_contra hh
  have hn := spiralPolynomial_neg_of_le hs.1 (le_of_not_gt hh)
  rw [hs.2] at hn
  linarith

/-- Article: the spiral exponent is strictly greater than log q. -/
theorem log_q_lt_log_factor {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Real.log q < Real.log (factor q) :=
  Real.log_lt_log hq (q_lt_factor hq hq1)

end polyak.Spiral
