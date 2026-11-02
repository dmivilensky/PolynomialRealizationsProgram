import krylov.XR.LocalRitzBounds
import krylov.XR.RadauUpperSource
import krylov.XR.AdequacyFloor

/-!
Article: main_krylov, prop:floor and apG:radau-adequate.
Use: transfer the actual shifted-Schur formula from genuine unit steps
back to the arbitrary raw steps used by ModelStep. No endpoint accuracy
or positive shifted inverse is assumed. Source: diagonal congruence of the
totalized inverse; positivity on the source domain is supplied separately
by the constructive physical Radau theorem.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant krylov.Convergence
open krylov.Methods hiding unitWindow unitWindow_norm unitWindow_diagonal_unit
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

theorem upperConsistencyCoefficient_rescale
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : IsUnit (diagonal c).det)
    (d : EuclideanSpace ℝ (Fin n)) (upper : ℝ) :
    upperConsistencyCoefficient (rescaleWindow s c) (rescaleModel T c) d upper =
      upperConsistencyCoefficient s T d upper := by
  have hpen : upper • crossGram (rescaleWindow s c) (rescaleWindow s c) - rescaleModel T c =
      rescaleModel (upper • crossGram s s - T) c := by
    rw [window_crossGram_rescale]
    ext i j
    simp only [rescaleModel, diagonal_mul, mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  unfold upperConsistencyCoefficient
  rw [hpen, coordinates_rescale]
  congr 2
  rw [← rescaleModel_quadratic]
  rw [show rescaleModel ((rescaleModel (upper • crossGram s s - T) c)⁻¹) c =
    (upper • crossGram s s - T)⁻¹ from rescaleModel_inverse _ c hc]

/-- The literal lower shifted-Schur endpoint has the same exact raw-pair
normalization invariance as the upper endpoint. -/
theorem lowerConsistencyCoefficient_rescale
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : IsUnit (diagonal c).det)
    (d : EuclideanSpace ℝ (Fin n)) (upper : ℝ) :
    lowerConsistencyCoefficient (rescaleWindow s c) (rescaleModel T c) d upper =
      lowerConsistencyCoefficient s T d upper := by
  have hpen : rescaleModel T c - upper • crossGram (rescaleWindow s c) (rescaleWindow s c) =
      rescaleModel (T - upper • crossGram s s) c := by
    rw [window_crossGram_rescale]
    ext i j
    simp only [rescaleModel, diagonal_mul, mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  unfold lowerConsistencyCoefficient
  rw [hpen, coordinates_rescale]
  congr 2
  rw [← rescaleModel_quadratic]
  rw [show rescaleModel ((rescaleModel (T - upper • crossGram s s) c)⁻¹) c =
    (T - upper • crossGram s s)⁻¹ from rescaleModel_inverse _ c hc]

/-- A genuine upper consistency endpoint in raw coordinates encloses the
true curvature; every premise is primitive physical data or a spectral
class margin. The algorithm's lower estimate is irrelevant here. -/
theorem rawWindow_upper_consistency_adequate
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i, s i ≠ 0)
    (d : EuclideanSpace ℝ (Fin n)) (hd : d ≠ 0)
    (a b upper sigma epsilon : ℝ) (ha : 0 < a) (hab : a ≤ b) (hupper : b < upper) (hb : 0 < b)
    (hsigma : 0 < sigma) (hsigma₁ : sigma ≤ 1) (he : 0 ≤ epsilon)
    (hHlo : (H - a • 1).PosSemidef) (hHhi : (b • 1 - H).PosSemidef)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ inner ℝ v (krylov.Reference.cgOperator H v))
    (hHnorm : ‖krylov.Reference.cgOperator H‖ ≤ b)
    (hgain : ∀ c : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 c‖ ^ 2 ≤ ‖combine (unitWindow s) c‖ ^ 2)
    (hy : ∀ i, ‖y i - krylov.Reference.cgOperator H (s i)‖ ≤ epsilon * ‖s i‖)
    (ho : ∀ i, inner ℝ (y i) d = 0)
    (hsmall : Real.sqrt p * epsilon ≤ a * sigma ^ 2 / 2)
    (hsmalllo : (p+1 : ℕ) * epsilon < (a-a/2) * (a*sigma^2/(2*b)))
    (hsmallhi : (p+1 : ℕ) * epsilon < (upper-b) * (a*sigma^2/(2*b))) :
    a ≤ upperConsistencyCoefficient s (latest (crossGram s y)) d upper ∧
      inner ℝ d (krylov.Reference.cgOperator H d) ≤
        upperConsistencyCoefficient s (latest (crossGram s y)) d upper * ‖d‖ ^ 2 ∧
      upperConsistencyCoefficient s (latest (crossGram s y)) d upper ≤ upper := by
  have hn := radau_upper_only_adequacy H hH (unitWindow s) (unitWindowImages s y)
    (unitWindow_norm s hs) d hd a b upper sigma epsilon ha hab hupper hb hsigma hsigma₁ he
    hHlo hHhi hlower hHnorm hgain
    (unitWindow_reference_error _ s y hs epsilon hy)
    (by intro i; change inner ℝ (‖s i‖⁻¹ • y i) d = 0; rw [real_inner_smul_left, ho, mul_zero])
    hsmall hsmalllo hsmallhi
  have heq : upperConsistencyCoefficient (unitWindow s)
      (latest (crossGram (unitWindow s) (unitWindowImages s y))) d upper =
      upperConsistencyCoefficient s (latest (crossGram s y)) d upper := by
    change upperConsistencyCoefficient (rescaleWindow s (fun i => ‖s i‖⁻¹))
      (ss1Model (rescaleWindow s (fun i => ‖s i‖⁻¹))
        (rescaleWindow y (fun i => ‖s i‖⁻¹))) d upper = _
    rw [ss1Model_rescale, upperConsistencyCoefficient_rescale _ _ _
      (unitWindow_diagonal_unit s hs)]
    rfl
  rw [heq] at hn
  exact hn

end
end krylov.XR
