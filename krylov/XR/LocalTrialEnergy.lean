import krylov.XR.LocalUniformStep
import krylov.XR.LocalCurvatureIntegral

/-!
Article: main_krylov, apG:local(c), actual trial-energy comparison.
Use: compare the genuine Hessian energy of the computed model trial with
its observed block model. The only approximation is the original physical
secant-error allowance; conjugacy is derived from the actual inverse solve.
Source: bilinear expansion and the actual observed normal/conjugacy equations.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The old observed image combination is exactly orthogonal to the
actually computed direction. -/
theorem modelDirection_combined_image_orthogonal (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hinv : IsUnit (crossGram y s).det)
    (g : E) (w : Fin p → ℝ) :
    inner ℝ (combine y w) (modelDirection s y T g) = 0 := by
  rw [real_inner_comm, inner_combine_coordinates,
    modelDirection_conjugate s y T hinv g, dotProduct_zero]

/-- The true old-window/new-direction Hessian coupling is small because
the genuine observed images are conjugate to the computed direction. -/
theorem modelDirection_true_cross_bound (H : E →L[ℝ] E) (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hinv : IsUnit (crossGram y s).det)
    (g : E) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) (w : Fin p → ℝ) :
    |inner ℝ (H (combine s w)) (modelDirection s y T g)| ≤
      frameBound p epsilon * ‖WithLp.toLp 2 w‖ * ‖modelDirection s y T g‖ := by
  have hcols (i : Fin p) : ‖H (s i) - y i‖ ≤ epsilon := by
    rw [norm_sub_rev]
    exact hy i
  have hsynth := synthesis_norm_of_columns (fun i => H (s i) - y i) epsilon he hcols w
  have hid : H (combine s w) - combine y w = combine (fun i => H (s i) - y i) w := by
    simp only [combine, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
  have hinner : inner ℝ (H (combine s w)) (modelDirection s y T g) =
      inner ℝ (H (combine s w) - combine y w) (modelDirection s y T g) := by
    rw [inner_sub_left, modelDirection_combined_image_orthogonal s y T hinv g w, sub_zero]
  rw [hinner, hid]
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_right hsynth (norm_nonneg _)).trans_eq (by ring))

/-- The old-window true Hessian energy differs from its actually solved
model energy by the primitive measured secant allowance. -/
theorem window_true_energy_error (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (w : Fin p → ℝ) :
    |inner ℝ (H (combine s w)) (combine s w) -
      w ⬝ᵥ (latest (crossGram s y) *ᵥ w)| ≤ (p : ℝ) * epsilon * ‖WithLp.toLp 2 w‖ ^ 2 := by
  have hb := coefficient_quadratic_norm_bound
    (latest (crossGram s y) - localReferenceGram H s) w
  have hn := local_latest_error_norm H hH s y hs he hy
  have hid : w ⬝ᵥ ((latest (crossGram s y) - localReferenceGram H s) *ᵥ w) =
      w ⬝ᵥ (latest (crossGram s y) *ᵥ w) - inner ℝ (H (combine s w)) (combine s w) := by
    rw [sub_mulVec, dotProduct_sub, localReferenceGram, operatorGram_form]
  rw [hid, abs_sub_comm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hn (sq_nonneg _))

/-- Exact symmetric energy expansion for the actual window-plus-trial
vector. -/
theorem modelTrial_true_energy_expand (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (v d : E) (t : ℝ) :
    inner ℝ (H (v + t • d)) (v + t • d) =
      inner ℝ (H v) v + 2 * t * inner ℝ (H v) d + t ^ 2 * inner ℝ (H d) d := by
  have hc : inner ℝ (H d) v = inner ℝ (H v) d :=
    (real_inner_comm _ _).trans (hH v d).symm
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hc]
  ring

/-- The true Hessian energy of the actually computed trial differs from
the old model energy plus the true new-direction energy by O(epsilon),
with a source-only dimension constant. -/
theorem modelTrial_true_energy_error (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (hinv : IsUnit (crossGram y s).det) (g : E) (c epsilon : ℝ)
    (he : 0 ≤ epsilon) (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) :
    let T := latest (crossGram s y)
    let w := modelCoefficients s T g
    let d := modelDirection s y T g
    let t := modelTrialLength s y T g c
    |inner ℝ (H (modelTrialStep s y T g c)) (modelTrialStep s y T g c) -
      (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (H d) d)| ≤
      (2 * (p : ℝ) + 1) * epsilon *
        (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) := by
  dsimp only
  let T := latest (crossGram s y)
  let w := modelCoefficients s T g
  let d := modelDirection s y T g
  let t := modelTrialLength s y T g c
  change |inner ℝ (H (modelTrialStep s y T g c)) (modelTrialStep s y T g c) -
      (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (H d) d)| ≤
    (2 * (p : ℝ) + 1) * epsilon * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2)
  have hw := window_true_energy_error H hH s y hs epsilon he hy w
  change |inner ℝ (H (combine s w)) (combine s w) - w ⬝ᵥ (T *ᵥ w)| ≤
    (p : ℝ) * epsilon * ‖WithLp.toLp 2 w‖ ^ 2 at hw
  have hc := modelDirection_true_cross_bound H s y T hinv g epsilon he hy w
  change |inner ℝ (H (combine s w)) d| ≤ frameBound p epsilon * ‖WithLp.toLp 2 w‖ * ‖d‖ at hc
  have hid : inner ℝ (H (modelTrialStep s y T g c)) (modelTrialStep s y T g c) -
      (w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (H d) d) =
      (inner ℝ (H (combine s w)) (combine s w) - w ⬝ᵥ (T *ᵥ w)) +
        2 * t * inner ℝ (H (combine s w)) d := by
    rw [modelTrialStep, modelTrial_true_energy_expand H hH]
    dsimp only [w, d, t, modelVirtualCorrection]
    ring
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
  have hmiss : 0 ≤ (p : ℝ) * epsilon * (t ^ 2 * ‖d‖ ^ 2) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg p) he) (mul_nonneg (sq_nonneg t) (sq_nonneg ‖d‖))
  nlinarith

end
end krylov.XR
