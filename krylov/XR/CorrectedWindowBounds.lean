import krylov.XR.CorrectedPairBounds
import krylov.XR.LocalGeneralModel
import krylov.XR.LocalRelative
import krylov.XR.LocalRawWindow

/-!
Article: main_krylov, cor:xrF, actual corrected-window approximation.
Use: normalize the genuinely computed gated diagonal with no short-step
loss. The entire actual corrected model approaches the same true Hessian
Gram as the ordinary secants; the value gate may still clip terms.
Source: true scalar-defect bounds and the finite spectral/Frobenius estimate.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A bound in genuine squared-step units survives normalization exactly. -/
theorem normalized_scalar_bound (s : E) (hs : s ≠ 0) (t b : ℝ)
    (ht : |t| ≤ b * ‖s‖ ^ 2) : |‖s‖⁻¹ * t * ‖s‖⁻¹| ≤ b := by
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have he : |‖s‖⁻¹ * t * ‖s‖⁻¹| = |t| / ‖s‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_inv, abs_norm]
    ring
  rw [he]
  exact (div_le_iff₀ (sq_pos_of_pos hn)).2 ht

/-- Genuine relative image errors and actual value-diagonal budgets imply
the complete normalized corrected model error in the original Hessian
coordinates, independently of the length of any stored observation. -/
theorem storedValueModel_normalized_error
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (W : List (PairObservation E)) (hs : ∀ i, storedSteps W i ≠ 0)
    (epsilon b : ℝ) (he : 0 ≤ epsilon) (hb : 0 ≤ b)
    (hy : ∀ i, ‖storedImages W i - H (storedSteps W i)‖ ≤ epsilon * ‖storedSteps W i‖)
    (hvalue : ∀ i : Fin W.length, |storedValueTerm W i| ≤ b * ‖storedSteps W i‖ ^ 2) :
    ‖rescaleModel (storedValueModel W) (fun i => ‖storedSteps W i‖⁻¹) -
      localReferenceGram H (krylov.Convergence.unitWindow (storedSteps W))‖ ≤
        (W.length : ℝ) * (epsilon + b) := by
  let s := storedSteps W
  let y := storedImages W
  let sn := krylov.Convergence.unitWindow s
  let yn := krylov.Convergence.unitWindowImages s y
  let c := fun i => ‖s i‖⁻¹
  have herror := unitWindow_reference_error H s y hs epsilon hy
  have hraw : rescaleModel (storedModel W) c = latest (crossGram sn yn) :=
    (krylov.Convergence.ss1Model_rescale s y c).symm
  have hd : rescaleModel (diagonal (storedValueTerm W)) c =
      diagonal (fun i => c i * storedValueTerm W i * c i) := by
    ext i j
    simp only [rescaleModel, mul_diagonal, diagonal_apply]
    split_ifs with hij
    · subst j
      rfl
    · simp
  have hdecomp : rescaleModel (storedValueModel W) c - localReferenceGram H sn =
      (latest (crossGram sn yn) - localReferenceGram H sn) -
        diagonal (fun i => c i * storedValueTerm W i * c i) := by
    have heq : rescaleModel (storedValueModel W) c =
        rescaleModel (storedModel W) c - rescaleModel (diagonal (storedValueTerm W)) c := by
      simp only [storedValueModel, rescaleModel, Matrix.mul_sub, Matrix.sub_mul]
    rw [heq, hraw, hd]
    abel
  rw [hdecomp]
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ (add_nonneg he hb)
  intro i j
  have hentry : |(latest (crossGram sn yn) - localReferenceGram H sn) i j| ≤ epsilon := by
    rw [local_latest_error_entry H hH sn yn i j]
    exact (abs_real_inner_le_norm _ _).trans (by
      rw [show ‖sn (min i j)‖ = 1 from krylov.Convergence.unitWindow_norm s hs (min i j), one_mul]
      exact herror (max i j))
  have hdiag : |diagonal (fun i => c i * storedValueTerm W i * c i) i j| ≤ b := by
    by_cases hij : i = j
    · subst j
      rw [diagonal_apply_eq]
      exact normalized_scalar_bound (s i) (hs i) _ b (hvalue i)
    · simpa only [diagonal_apply, hij, ite_false, abs_zero] using hb
  exact (abs_sub _ _).trans (add_le_add hentry hdiag)

/-- The original unnormalized corrected model is symmetric, including
when its scalar oversized-term gate clips some entries. -/
theorem storedValueModel_isSymm (W : List (PairObservation E)) : (storedValueModel W).IsSymm := by
  exact (latest_isSymm _).sub (isSymm_diagonal _)

/-- Actual model selection preserves a common genuine error allowance,
whether the value gate succeeds or falls back to the ordinary model. -/
theorem selectedModel_normalized_error (P : Parameters)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (W : List (PairObservation E)) (hs : ∀ i, storedSteps W i ≠ 0)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hy : ∀ i, ‖storedImages W i - H (storedSteps W i)‖ ≤ epsilon * ‖storedSteps W i‖)
    (hmodel : ‖rescaleModel (storedValueModel W) (fun i => ‖storedSteps W i‖⁻¹) -
      localReferenceGram H (krylov.Convergence.unitWindow (storedSteps W))‖ ≤ (W.length : ℝ) * epsilon) :
    ‖rescaleModel (selectedModel P W) (fun i => ‖storedSteps W i‖⁻¹) -
      localReferenceGram H (krylov.Convergence.unitWindow (storedSteps W))‖ ≤ (W.length : ℝ) * epsilon := by
  classical
  unfold selectedModel
  split
  · exact hmodel
  · rw [show rescaleModel (storedModel W) (fun i => ‖storedSteps W i‖⁻¹) =
      latest (crossGram (krylov.Convergence.unitWindow (storedSteps W))
        (krylov.Convergence.unitWindowImages (storedSteps W) (storedImages W))) from
      (krylov.Convergence.ss1Model_rescale (storedSteps W) (storedImages W) _).symm]
    exact local_latest_error_norm H hH _ _ (krylov.Convergence.unitWindow_norm _ hs) he
      (unitWindow_reference_error H _ _ hs epsilon hy)

end
end krylov.XR
