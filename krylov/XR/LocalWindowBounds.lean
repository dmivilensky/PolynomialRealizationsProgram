import krylov.XR.ModelStep
import krylov.Convergence.WindowModelBounds
import krylov.Correction.ObservedSearchDomains

/-!
Article: main_krylov, apG:local(a), genuine rectangular observed-window errors.
Use: quantify the actual latest and nonsymmetric conjugacy models against
the same true Hessian on arbitrary p-column windows. The data errors are
physical secant errors; model closeness is proved rather than postulated.
Source: the latest-information selector (Burdakov83), Cauchy--Schwarz, and
the spectral/Frobenius estimate already used for actual SS1 windows.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- True Hessian Gram matrix, in the same coefficient space as the actual
observed model. -/
def localReferenceGram (H : E →L[ℝ] E) (s : Fin p → E) : Matrix (Fin p) (Fin p) ℝ :=
  crossGram (fun i => H (s i)) s

/-- Every actual latest-model error entry is the genuinely observed error
of its newer secant column, paired with the older unit step. -/
theorem local_latest_error_entry (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (i j : Fin p) :
    (latest (crossGram s y) - localReferenceGram H s) i j =
      inner ℝ (s (min i j)) (y (max i j) - H (s (max i j))) := by
  simp only [Matrix.sub_apply, latest, crossGram, inner_sub_right, localReferenceGram]
  congr 1
  rcases le_total i j with hij | hji
  · simp only [min_eq_left hij, max_eq_right hij]
    exact hH _ _
  · simp only [min_eq_right hji, max_eq_left hji]
    exact real_inner_comm _ _

/-- Actual unit-column errors imply the dimension-times-error spectral
bound for the observed latest-information model, with general H*. -/
theorem local_latest_error_norm (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) :
    ‖latest (crossGram s y) - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ he
  intro i j
  rw [local_latest_error_entry H hH s y i j]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
    simpa only [hs, one_mul, Real.norm_eq_abs] using hy (max i j))

/-- The actual nonsymmetric conjugacy matrix has the same physical
dimension-times-error bound against the true Hessian Gram matrix. -/
theorem local_conjugacy_error_norm (H : E →L[ℝ] E)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) :
    ‖crossGram y s - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ he
  intro i j
  change |inner ℝ (y i) (s j) - inner ℝ (H (s i)) (s j)| ≤ epsilon
  rw [← inner_sub_left]
  have hb := norm_inner_le_norm (𝕜 := ℝ) (y i - H (s i)) (s j)
  rw [Real.norm_eq_abs, hs j, mul_one] at hb
  exact hb.trans (hy i)

/-- The original chronological pairing matrix has the same actual
dimension-times-error estimate against the true Hessian Gram. -/
theorem local_pairing_error_norm (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) :
    ‖crossGram s y - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ he
  intro i j
  change |inner ℝ (s i) (y j) - inner ℝ (H (s i)) (s j)| ≤ epsilon
  have hh := hH (s i) (s j)
  change inner ℝ (H (s i)) (s j) = inner ℝ (s i) (H (s j)) at hh
  rw [hh, ← inner_sub_right]
  have hb := norm_inner_le_norm (𝕜 := ℝ) (s i) (y j - H (s j))
  rw [Real.norm_eq_abs, hs i, one_mul] at hb
  exact hb.trans (hy j)

/-- The real observed normal-equation inconsistency is small because both
its terms approximate the same true Hessian Gram. -/
theorem local_pairing_latest_gap (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) :
    ‖crossGram s y - latest (crossGram s y)‖ ≤ 2 * (p : ℝ) * epsilon := by
  have hid : crossGram s y - latest (crossGram s y) =
      (crossGram s y - localReferenceGram H s) -
        (latest (crossGram s y) - localReferenceGram H s) := by abel
  rw [hid]
  exact (norm_sub_le _ _).trans (by
    linarith [local_pairing_error_norm H hH s y hs he hy,
      local_latest_error_norm H hH s y hs he hy])

/-- The true skew inconsistency has its printed 2p epsilon bound. -/
theorem local_defect_norm (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) :
    ‖defect (crossGram s y)‖ ≤ 2 * (p : ℝ) * epsilon := by
  have hsymmetric : (localReferenceGram H s).IsSymm := by
    ext i j
    exact ((hH _ _).trans (real_inner_comm _ _)).symm
  have hraw : crossGram y s = (crossGram s y)ᵀ := by
    ext i j
    exact real_inner_comm _ _
  have hb := local_conjugacy_error_norm H s y hs he hy
  have htr : ‖crossGram s y - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon := by
    rw [hraw] at hb
    have heq : (crossGram s y)ᵀ - localReferenceGram H s =
        (crossGram s y - localReferenceGram H s)ᵀ := by
      rw [transpose_sub, hsymmetric.eq]
    have hn : ‖(crossGram s y - localReferenceGram H s)ᵀ‖ =
        ‖crossGram s y - localReferenceGram H s‖ := by
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
        norm_star (crossGram s y - localReferenceGram H s)
    rw [heq, hn] at hb
    exact hb
  have heq : defect (crossGram s y) =
      (crossGram s y - localReferenceGram H s) - (crossGram y s - localReferenceGram H s) := by
    rw [hraw, defect]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The actual virtual gradient's old-step coordinates are exactly the
observed pairing inconsistency times the computed model coefficients. -/
theorem modelVirtualGradient_coordinates (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det) (g : E) :
    coordinates s (modelVirtualGradient s y T g) =
      (crossGram s y - T) *ᵥ modelCoefficients s T g := by
  have hadd : coordinates s (g + combine y (modelCoefficients s T g)) =
      coordinates s g + coordinates s (combine y (modelCoefficients s T g)) := by
    ext i
    simp only [coordinates, inner_add_right, Pi.add_apply]
  rw [modelVirtualGradient, hadd, coordinates_combine, sub_mulVec,
    modelCoefficients_normal s T hT g]
  abel

end
end krylov.XR
