import krylov.Convergence.WindowNormalization
import krylov.Convergence.WindowModelBounds
import krylov.XR.LocalDimensionConstants
import krylov.XR.SkewCongruence

/-!
Article: main_krylov, apG:local, exact original-pair normalization.
Use: transport the primitive unit-column estimates to the actual arbitrary
nonzero steps retained by XR. All physical virtual/trial steps and the
actual Hermitian window test are unchanged by simultaneous pair scaling.
Source: exact diagonal congruence of the genuine observed inverse solves.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Convergence
open scoped InnerProductSpace ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The true virtual scalar model correction is invariant under genuine
nonzero column scaling, for arbitrary rectangular windows. -/
theorem modelVirtualCorrection_rescale (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : IsUnit (diagonal c).det) (g : E) :
    modelVirtualCorrection (rescaleWindow s c) (rescaleModel T c) g = modelVirtualCorrection s T g :=
  modelCorrection_rescale s T c hc g

/-- Simultaneously rescaling measured images preserves the actual
extrapolated gradient, rather than only its projected coordinates. -/
theorem modelVirtualGradient_rescale (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : IsUnit (diagonal c).det) (g : E) :
    modelVirtualGradient (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) g =
      modelVirtualGradient s y T g := by
  unfold modelVirtualGradient
  congr 1
  rw [combine_rescale, modelCoefficients, coordinates_rescale, mulVec_neg,
    mulVec_mulVec, mulVec_mulVec, rescaleModel_inverse T c hc]
  rfl

/-- The actual observed image-conjugate new direction is unchanged. -/
theorem modelDirection_rescale (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : IsUnit (diagonal c).det) (g : E) :
    modelDirection (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) g =
      modelDirection s y T g := by
  rw [modelDirection, modelVirtualGradient_rescale s y T c hc]
  exact conjugacyDirection_rescale s y c hc _

/-- Any physical new-curvature estimate gives the same actual block
trial after the original pairs are normalized. -/
theorem modelTrialStep_rescale (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : IsUnit (diagonal c).det) (g : E) (curvature : ℝ) :
    modelTrialStep (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) g curvature =
      modelTrialStep s y T g curvature := by
  unfold modelTrialStep modelTrialLength
  rw [modelVirtualCorrection_rescale s T c hc, modelDirection_rescale s y T c hc]

/-- Zero-direction and ordinary branches both preserve the true local
physical model step under nonzero individual pair scaling. -/
theorem localModelStep_rescale (s y : Fin p → E) (c : Fin p → ℝ)
    (hc : IsUnit (diagonal c).det) (g : E) (curvature : ℝ) :
    localModelStep (rescaleWindow s c) (rescaleWindow y c) g curvature =
      localModelStep s y g curvature := by
  classical
  unfold localModelStep
  dsimp only
  rw [show latest (crossGram (rescaleWindow s c) (rescaleWindow y c)) =
      rescaleModel (latest (crossGram s y)) c from ss1Model_rescale s y c]
  rw [modelDirection_rescale s y _ c hc, modelVirtualCorrection_rescale s _ c hc,
    modelTrialStep_rescale s y _ c hc]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The actual observed skew matrix has the same diagonal congruence. -/
theorem defect_rescaleModel (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin p → ℝ) :
    defect (rescaleModel M c) = rescaleModel (defect M) c := by
  simp only [defect, rescaleModel, transpose_mul, diagonal_transpose]
  noncomm_ring

/-- The genuine complex window test is exactly invariant under arbitrary
nonzero pair normalizers. -/
theorem windowUnrefuted_rescale (theta : ℝ) (s y : Fin p → E) (c : Fin p → ℝ)
    (hc : IsUnit (diagonal c).det) :
    windowUnrefuted theta (crossGram (rescaleWindow s c) (rescaleWindow y c)) ↔
      windowUnrefuted theta (crossGram s y) := by
  rw [window_crossGram_rescale, windowUnrefuted, windowUnrefuted]
  rw [hermitianWindowMatrix_eq, hermitianWindowMatrix_eq]
  rw [show latest (rescaleModel (crossGram s y) c) =
      rescaleModel (latest (crossGram s y)) c from latest_diagonal_congruence _ c,
    defect_rescaleModel]
  simpa only [rescaleModel, diagonal_transpose] using
    hermitianTest_congruence_iff theta (latest (crossGram s y)) (defect (crossGram s y)) (diagonal c) hc

end
end krylov.XR
