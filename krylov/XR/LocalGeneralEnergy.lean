import krylov.XR.LocalGeneralModel
import krylov.XR.LocalMeasuredQuotient

/-!
Article: main_krylov, apG:local(c) and cor:xrF, general-model Taylor energy.
Use: replace the latest model by any genuinely accurate selected model
without changing the printed source-only local constants. The mixed true
Hessian term is controlled by actual observed conjugacy, independently
of which scalar value diagonal the algorithm selected.
Source: true coefficient Gram approximation and the genuine weighted
Taylor identity; no function-value quotient is an input hypothesis.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- A true selected-model error controls the old physical Hessian energy. -/
theorem window_true_energy_error_with (H : E →L[ℝ] E) (s : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (epsilon : ℝ)
    (hmodel : ‖T - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon) (w : Fin p → ℝ) :
    |inner ℝ (H (combine s w)) (combine s w) - w ⬝ᵥ (T *ᵥ w)| ≤
      (p : ℝ) * epsilon * ‖WithLp.toLp 2 w‖ ^ 2 := by
  have hb := coefficient_quadratic_norm_bound (T - localReferenceGram H s) w
  rw [sub_mulVec, dotProduct_sub, localReferenceGram, operatorGram_form, abs_sub_comm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hmodel (sq_nonneg _))

/-- Genuine secants and a true general-model approximation give the same
component-energy error for the actually computed block trial. -/
theorem modelTrial_true_energy_error_with (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (hinv : IsUnit (crossGram y s).det) (g : E) (c epsilon : ℝ)
    (he : 0 ≤ epsilon) (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hmodel : ‖T - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon) :
    let w := modelCoefficients s T g
    let d := modelDirection s y T g
    let t := modelTrialLength s y T g c
    |inner ℝ (H (modelTrialStep s y T g c)) (modelTrialStep s y T g c) -
      (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (H d) d)| ≤
      (2 * (p : ℝ) + 1) * epsilon * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) := by
  let w := modelCoefficients s T g
  let d := modelDirection s y T g
  let t := modelTrialLength s y T g c
  have hw := window_true_energy_error_with H s T epsilon hmodel w
  have hc := modelDirection_true_cross_bound H s y T hinv g epsilon he hy w
  have hid : inner ℝ (H (modelTrialStep s y T g c)) (modelTrialStep s y T g c) -
      (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (H d) d) =
      (inner ℝ (H (combine s w)) (combine s w) - w ⬝ᵥ (T *ᵥ w)) +
        2 * t * inner ℝ (H (combine s w)) d := by
    rw [modelTrialStep, modelTrial_true_energy_expand H hH]
    dsimp only [w, d, t, modelVirtualCorrection]
    ring
  dsimp only
  rw [hid]
  have hab := abs_add_le
    (inner ℝ (H (combine s w)) (combine s w) - w ⬝ᵥ (T *ᵥ w))
    (2 * t * inner ℝ (H (combine s w)) d)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hab
  have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * |t|)
  apply hab.trans
  have hyoung : 2 * |t| * ‖WithLp.toLp 2 w‖ * ‖d‖ ≤
      ‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2 := by
    nlinarith [sq_nonneg (‖WithLp.toLp 2 w‖ - |t| * ‖d‖), sq_abs t]
  dsimp only [frameBound] at hc'
  have hm := mul_le_mul_of_nonneg_left hyoung
    (mul_nonneg (by positivity : 0 ≤ (p : ℝ) + 1) he)
  have hmiss : 0 ≤ (p : ℝ) * epsilon * (t ^ 2 * ‖d‖ ^ 2) := by positivity
  nlinarith

/-- The true weighted Taylor curvature has its original uniform component
error for any selected model approximating the genuine Hessian Gram. -/
theorem modelTrial_weighted_curvature_error_with (H : E → E →L[ℝ] E)
    (Hstar : E →L[ℝ] E) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (hs : ∀ i, ‖s i‖ = 1)
    (hinv : IsUnit (crossGram y s).det) (g x : E) (c epsilon : ℝ)
    (he : 0 ≤ epsilon) (hy : ∀ i, ‖y i - Hstar (s i)‖ ≤ epsilon)
    (hmodel : ‖T - localReferenceGram Hstar s‖ ≤ (p : ℝ) * epsilon)
    (hH : ContinuousOn (fun t : ℝ => H (x + t • modelTrialStep s y T g c)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (x + t • modelTrialStep s y T g c) - Hstar‖ ≤ epsilon) :
    let w := modelCoefficients s T g
    let d := modelDirection s y T g
    let t := modelTrialLength s y T g c
    |weightedCurvature H x (modelTrialStep s y T g c) -
      (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (Hstar d) d)| ≤
      curvatureErrorConstant p * epsilon * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) := by
  let w := modelCoefficients s T g
  let d := modelDirection s y T g
  let t := modelTrialLength s y T g c
  let u := modelTrialStep s y T g c
  have hW := weightedCurvature_error H Hstar x u epsilon he hH herror
  have hE := modelTrial_true_energy_error_with Hstar hHstar s y T hinv g c epsilon he hy hmodel
  dsimp only at hE ⊢
  have hN := modelTrialStep_norm_sq s y T g c (fun i => (hs i).le)
  have ht := (abs_sub_le (weightedCurvature H x u) (inner ℝ (Hstar u) u)
    (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (Hstar d) d)).trans (add_le_add hW hE)
  apply ht.trans
  have hm := mul_le_mul_of_nonneg_left hN he
  have ha : 0 ≤ ‖WithLp.toLp 2 w‖ ^ 2 := sq_nonneg _
  have hd : 0 ≤ t ^ 2 * ‖d‖ ^ 2 := by positivity
  have hframe : 0 ≤ (frameBound p 1) ^ 2 := sq_nonneg _
  dsimp only [curvatureErrorConstant]
  nlinarith [mul_nonneg he ha, mul_nonneg he hd,
    mul_nonneg (mul_nonneg he hframe) ha, mul_nonneg (mul_nonneg he hframe) hd]

end
end krylov.XR
