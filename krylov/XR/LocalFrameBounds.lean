import krylov.XR.LocalCoercivity

/-!
Article: main_krylov, apG:local(b,c), bounded actual rectangular analysis.
Use: control observed coordinate vectors, real coefficient solves and
physical synthesis by the same dimension/column constants.
Source: finite Cauchy--Schwarz and the proved Gram synthesis identity.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- A deliberately coarse constant, uniform also for empty windows. -/
def frameBound (p : ℕ) (K : ℝ) : ℝ := ((p : ℝ) + 1) * K

/-- True column norm bounds control the actual coefficient Gram norm. -/
theorem gram_norm_of_columns (s : Fin p → E) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ i, ‖s i‖ ≤ K) : ‖crossGram s s‖ ≤ (frameBound p K) ^ 2 := by
  have hb : ‖crossGram s s‖ ≤ (p : ℝ) * K ^ 2 := by
    apply (spectral_le_hsNorm _).trans
    apply hsNorm_le_dimension _ (sq_nonneg K)
    intro i j
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
      simpa only [Real.norm_eq_abs, pow_two] using
        mul_le_mul (hs i) (hs j) (norm_nonneg _) hK)
  apply hb.trans
  dsimp only [frameBound]
  nlinarith [Nat.cast_nonneg (α := ℝ) p, sq_nonneg ((p : ℝ) * K), sq_nonneg K]

/-- Real physical synthesis has the uniform dimension/column bound. -/
theorem synthesis_norm_of_columns (s : Fin p → E) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ i, ‖s i‖ ≤ K) (w : Fin p → ℝ) :
    ‖combine s w‖ ≤ frameBound p K * ‖WithLp.toLp 2 w‖ := by
  have hb : 0 ≤ frameBound p K := mul_nonneg (by positivity) hK
  have h := combine_norm_le s w (sq_nonneg (frameBound p K)) (gram_norm_of_columns s K hK hs)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hb] using h

/-- Real observed coordinate analysis has the same uniform bound. -/
theorem analysis_norm_of_columns (s : Fin p → E) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ i, ‖s i‖ ≤ K) (g : E) :
    ‖WithLp.toLp 2 (coordinates s g)‖ ≤ frameBound p K * ‖g‖ := by
  have hS := synthesis_norm_of_columns s K hK hs (coordinates s g)
  have hi := real_inner_le_norm (combine s (coordinates s g)) g
  rw [combine_inner_coordinates] at hi
  change inner ℝ (WithLp.toLp 2 (coordinates s g)) (WithLp.toLp 2 (coordinates s g)) ≤ _ at hi
  rw [real_inner_self_eq_norm_sq] at hi
  have hp := mul_le_mul_of_nonneg_right hS (norm_nonneg g)
  by_cases hz : WithLp.toLp 2 (coordinates s g) = 0
  · rw [hz, norm_zero]
    unfold frameBound
    positivity
  · apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)).mp
    calc
      _ = ‖WithLp.toLp 2 (coordinates s g)‖ ^ 2 := by ring
      _ ≤ frameBound p K * ‖WithLp.toLp 2 (coordinates s g)‖ * ‖g‖ := hi.trans hp
      _ = _ := by ring

/-- Actual image norms follow from the genuine true-Hessian norm and
physical measured secant errors on normalized steps. -/
theorem image_norm_of_secant_error (H : E →L[ℝ] E) (s y : Fin p → E)
    (hs : ∀ i, ‖s i‖ = 1) (upper epsilon : ℝ) (hH : ‖H‖ ≤ upper)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) (i : Fin p) :
    ‖y i‖ ≤ upper + epsilon := by
  have ht := norm_sub_le (y i - H (s i)) (-(H (s i)))
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  have ho := (H.le_opNorm (s i)).trans
    (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  rw [hs i, mul_one] at ho
  linarith [hy i]

/-- The computed coefficient solve has its genuine inverse/analysis bound. -/
theorem modelCoefficients_norm_bound (s : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hs : ∀ i, ‖s i‖ ≤ K) (hT : ‖T⁻¹‖ ≤ C) (g : E) :
    ‖WithLp.toLp 2 (modelCoefficients s T g)‖ ≤ C * frameBound p K * ‖g‖ := by
  have he : WithLp.toLp 2 (modelCoefficients s T g) =
      -(Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ (WithLp.toLp 2 (coordinates s g))) := by
    ext i
    rfl
  rw [he, norm_neg]
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹).le_opNorm
    (WithLp.toLp 2 (coordinates s g))
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  exact ho.trans ((mul_le_mul hT (analysis_norm_of_columns s K hK hs g)
    (norm_nonneg _) hC).trans_eq (by ring))

/-- Actual conjugacy coefficients satisfy the corresponding measured-image
bound, independent of any desired direction behavior. -/
theorem conjugacyCoefficients_norm_bound (s y : Fin p → E)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hy : ∀ i, ‖y i‖ ≤ K)
    (hinv : ‖(crossGram y s)⁻¹‖ ≤ C) (g : E) :
    ‖WithLp.toLp 2 (conjugacyCoefficients s y g)‖ ≤ C * frameBound p K * ‖g‖ := by
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) (crossGram y s)⁻¹).le_opNorm
    (WithLp.toLp 2 (coordinates y g))
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  change ‖WithLp.toLp 2 (conjugacyCoefficients s y g)‖ ≤ _ at ho
  exact ho.trans ((mul_le_mul hinv (analysis_norm_of_columns y K hK hy g)
    (norm_nonneg _) hC).trans_eq (by ring))

end
end krylov.XR
