import jacobi.Variational.Problem
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
The regularized logarithm has a genuine spectral pole. Its real branch is
used only below that pole; FredholmSpectrum assigns infinity at the pole.
Source: elementary differential calculus for -log(1-sx)-sx.
Use: FredholmSpectrum sums this branch only for subcritical eigenvalues.
-/
namespace jacobi.Variational
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The real branch of the regularized spectral logarithm.
Use: FredholmSpectrum sums this branch only for subcritical eigenvalues.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def fredholmLog (s x : ℝ) : ℝ := -log (1-s*x)-s*x

/-- Actual derivative of the regularized logarithm below its pole.
Use: all quantitative Fredholm continuity and tail estimates.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: differentiate the logarithm and collect the two rational terms. -/
theorem fredholmLog_hasDerivAt {s x : ℝ} (hx : s*x < 1) :
    HasDerivAt (fredholmLog s) (s^2*x/(1-s*x)) x := by
  have h := (((hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul s)).log
    (by linarith : 1-s*x ≠ 0)).neg.sub ((hasDerivAt_id x).const_mul s)
  convert h using 1
  · rfl
  · change s^2*x/(1-s*x) = -((0-s*1)/(1-s*x))-s*1
    field_simp [show 1-s*x ≠ 0 by linarith]
    ring

/-- The real branch vanishes at zero.
Use: converts scalar secant estimates into summable spectral bounds.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: log(1)=0. -/
@[simp] theorem fredholmLog_zero (s : ℝ) : fredholmLog s 0 = 0 := by
  simp [fredholmLog]

/-- Positivity of the regularized logarithm throughout its real domain.
Use: matches the real spectral sum with the extended nonnegative sum.
Article: jacobi, Lemma D.1.
Proof: apply log(z)≤z-1 with z=1-sx>0. -/
theorem fredholmLog_nonneg {s x : ℝ} (hx : s*x < 1) : 0 ≤ fredholmLog s x := by
  have h := log_le_sub_one_of_pos (by linarith : 0 < 1-s*x)
  dsimp [fredholmLog]
  linarith

/-- Monotonicity on the nonnegative subcritical branch.
Use: ordering of density spectra orders the Fredholm functional.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the actual derivative s²x/(1-sx) is nonnegative on the interval. -/
theorem fredholmLog_mono {s a b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b)
    (hba : b ≤ a) (ha : s*a < 1) : fredholmLog s b ≤ fredholmLog s a := by
  -- All intermediate points stay strictly below the same pole.
  have hd (x : ℝ) (hx : x ∈ Icc b a) :=
    fredholmLog_hasDerivAt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx.2 hs) ha)
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc b a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [(hd x (interior_subset hx)).deriv]
      exact div_nonneg (mul_nonneg (sq_nonneg s) (hb.trans (interior_subset hx).1))
        (by have h := mul_le_mul_of_nonneg_left (interior_subset hx).2 hs; linarith))
  exact hm ⟨le_rfl,hba⟩ ⟨hba,le_rfl⟩ hba

/-- A uniform pole margin gives the printed scalar Lipschitz bound.
Use: spectral l1 convergence transfers regularized logarithmic observations.
Article: jacobi, Lemma D.1.
Proof: bound the genuine derivative on the interval containing both arguments. -/
theorem fredholmLog_lipschitz {s ε a b : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsa : s*a ≤ 1-ε) (hsb : s*b ≤ 1-ε) :
    |fredholmLog s a-fredholmLog s b| ≤ (s/ε)*|a-b| := by
  -- The convex interval avoids the pole, including when s or either eigenvalue is zero.
  let A := max a b
  have hA : s*A ≤ 1-ε := by
    dsimp [A]
    rcases le_total a b with h | h
    · simpa only [max_eq_right h] using hsb
    · simpa only [max_eq_left h] using hsa
  have hd (x : ℝ) (hx : x ∈ Icc 0 A) :=
    fredholmLog_hasDerivAt (s := s) (x := x)
      (by nlinarith [mul_le_mul_of_nonneg_left hx.2 hs])
  have h := (convex_Icc (0 : ℝ) A).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt)
    (fun x hx => show ‖s^2*x/(1-s*x)‖ ≤ s/ε from by
      have hxε : s*x ≤ 1-ε := (mul_le_mul_of_nonneg_left hx.2 hs).trans hA
      have hn := mul_nonneg (sq_nonneg s) hx.1
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hn (by linarith))]
      calc
        _ ≤ s^2*x/ε := div_le_div_of_nonneg_left hn hε (by linarith)
        _ ≤ s/ε := div_le_div_of_nonneg_right
          (by nlinarith [mul_le_mul_of_nonneg_left (show s*x ≤ 1 by linarith) hs]) hε.le)
    ⟨ha,le_max_left a b⟩ ⟨hb,le_max_right a b⟩
  simpa only [Real.norm_eq_abs,abs_sub_comm] using h

/-- A quadratic secant bound controls Fredholm tails by second-moment tails.
Use: proves Compactness (c) without a uniform global L1 tail bound.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the derivative of s²x²/(2ε)-f_s(x) is nonnegative below the pole margin. -/
theorem fredholmLog_quadratic {s ε a b : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hb : 0 ≤ b) (hba : b ≤ a) (hsa : s*a ≤ 1-ε) :
    fredholmLog s a-fredholmLog s b ≤ (s^2/(2*ε))*(a^2-b^2) := by
  -- Compare the two functions by their derivatives on the whole interval [b,a].
  have hd (x : ℝ) (hx : x ∈ Icc b a) :
      HasDerivAt (fun z => (s^2/(2*ε))*z^2-fredholmLog s z)
        ((s^2/ε)*x-s^2*x/(1-s*x)) x := by
    have hf := fredholmLog_hasDerivAt
      (by nlinarith [mul_le_mul_of_nonneg_left hx.2 hs] : s*x < 1)
    convert (((hasDerivAt_id x).pow 2).const_mul (s^2/(2*ε))).sub hf using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc b a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [(hd x (interior_subset hx)).deriv]
      have hx0 : 0 ≤ x := hb.trans (interior_subset hx).1
      have hmargin : ε ≤ 1-s*x := by
        nlinarith [mul_le_mul_of_nonneg_left (interior_subset hx).2 hs]
      have hdiv := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg s) hx0) hε hmargin
      have he : s^2*x/ε=(s^2/ε)*x := by ring
      rw [he] at hdiv
      exact sub_nonneg.mpr hdiv)
  have h := hm ⟨le_rfl,hba⟩ ⟨hba,le_rfl⟩ hba
  nlinarith

end
end jacobi.Variational
