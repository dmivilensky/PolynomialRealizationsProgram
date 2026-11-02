import krylov.XR.LocalFrameBounds

/-!
Article: main_krylov, apG:local(b,c), genuine extrapolated direction geometry.
Use: prove the small slope defect from the actual normal/conjugacy solves,
rather than assuming descent or a desired direction angle.
Source: exact observed coordinate equations and finite Cauchy--Schwarz.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual slope defect is exactly the old-step coordinate error
paired with the genuinely computed conjugacy coefficients. -/
theorem modelDirection_slope_defect (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det) (g : E) :
    inner ℝ (modelVirtualGradient s y T g) (modelDirection s y T g) +
      ‖modelVirtualGradient s y T g‖ ^ 2 =
    inner ℝ (WithLp.toLp 2 (conjugacyCoefficients s y (modelVirtualGradient s y T g)))
      (WithLp.toLp 2 ((crossGram s y - T) *ᵥ modelCoefficients s T g)) := by
  rw [← modelVirtualGradient_coordinates s y T hT g]
  rw [modelDirection, conjugacyDirection, inner_add_right, inner_neg_right,
    real_inner_self_eq_norm_sq]
  have hcancel (a b : ℝ) : -a + b + a = b := by ring
  rw [hcancel, inner_combine_coordinates]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The genuine slope defect has its exact coefficient/operator norm
bound, valid on any actual nonsingular observed model. -/
theorem modelDirection_slope_defect_norm (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det) (g : E) :
    |inner ℝ (modelVirtualGradient s y T g) (modelDirection s y T g) +
      ‖modelVirtualGradient s y T g‖ ^ 2| ≤
    ‖WithLp.toLp 2 (conjugacyCoefficients s y (modelVirtualGradient s y T g))‖ *
      ‖crossGram s y - T‖ * ‖WithLp.toLp 2 (modelCoefficients s T g)‖ := by
  rw [modelDirection_slope_defect s y T hT g]
  have hi := norm_inner_le_norm (𝕜 := ℝ)
    (WithLp.toLp 2 (conjugacyCoefficients s y (modelVirtualGradient s y T g)))
    (WithLp.toLp 2 ((crossGram s y - T) *ᵥ modelCoefficients s T g))
  rw [Real.norm_eq_abs] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_left
    (Matrix.l2_opNorm_mulVec (crossGram s y - T) (WithLp.toLp 2 (modelCoefficients s T g)))
    (norm_nonneg _)).trans_eq (by ring))

/-- Actual observed image norm and the genuine inverse bound turn the
exact slope identity into the uniform local geometric allowance. -/
theorem modelDirection_slope_defect_bound (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det) (g : E)
    (K C delta : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hy : ∀ i, ‖y i‖ ≤ K) (hinv : ‖(crossGram y s)⁻¹‖ ≤ C)
    (he : ‖crossGram s y - T‖ ≤ delta) :
    |inner ℝ (modelVirtualGradient s y T g) (modelDirection s y T g) +
      ‖modelVirtualGradient s y T g‖ ^ 2| ≤
    (C * frameBound p K * delta) * ‖WithLp.toLp 2 (modelCoefficients s T g)‖ *
      ‖modelVirtualGradient s y T g‖ := by
  have hb := conjugacyCoefficients_norm_bound s y K C hK hC hy hinv
    (modelVirtualGradient s y T g)
  apply (modelDirection_slope_defect_norm s y T hT g).trans
  calc
    _ ≤ (C * frameBound p K * ‖modelVirtualGradient s y T g‖) * delta *
        ‖WithLp.toLp 2 (modelCoefficients s T g)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hb he (norm_nonneg _)
        (by unfold frameBound; positivity)) (norm_nonneg _)
    _ = _ := by ring

/-- Actual direction norm is controlled by the extrapolated-gradient
norm, using only the real coefficient inverse and observed column bounds. -/
theorem modelDirection_norm_bound (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hs : ∀ i, ‖s i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ K)
    (hinv : ‖(crossGram y s)⁻¹‖ ≤ C) :
    ‖modelDirection s y T g‖ ≤
      (1 + frameBound p 1 * C * frameBound p K) * ‖modelVirtualGradient s y T g‖ := by
  have hb := conjugacyCoefficients_norm_bound s y K C hK hC hy hinv
    (modelVirtualGradient s y T g)
  have hS := synthesis_norm_of_columns s 1 (by norm_num) hs
    (conjugacyCoefficients s y (modelVirtualGradient s y T g))
  have ht := norm_add_le (-(modelVirtualGradient s y T g))
    (combine s (conjugacyCoefficients s y (modelVirtualGradient s y T g)))
  rw [norm_neg] at ht
  change ‖modelDirection s y T g‖ ≤ _ at ht
  have hsbound := hS.trans (mul_le_mul_of_nonneg_left hb (by unfold frameBound; positivity))
  nlinarith

end
end krylov.XR
