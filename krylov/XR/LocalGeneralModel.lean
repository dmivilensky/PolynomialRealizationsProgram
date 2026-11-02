import krylov.XR.LocalUniformStep
import krylov.XR.LocalNormalization

/-!
Article: main_krylov, apG:local and cor:xrF, general observed local model.
Use: the primitive physical step bounds depend only on approximation to
the genuine Hessian Gram matrix. Hence the same constants apply to the
actual corrected model after its source error has been proved small.
Inverse and coefficient domains below are derived from the primitive
model error, never supplied by an execution certificate.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual block step with any selected observed model. -/
def localModelStepWith (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (g : E) (c : ℝ) : E := by
  classical
  exact if modelDirection s y T g = 0 then modelVirtualCorrection s T g else modelTrialStep s y T g c

/-- General selected-model coercivity and inverse domains, all derived
from true Hessian positivity and a genuine normalized model error. -/
theorem local_general_model_domains (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hgain : ∀ w : Fin p → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hmodel : ‖T - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4) :
    (∀ w : Fin p → ℝ, localCoercivity mu sigma * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (T *ᵥ w)) ∧
      IsUnit T.det ∧ ‖T⁻¹‖ ≤ (localCoercivity mu sigma)⁻¹ ∧
      IsUnit (crossGram y s).det ∧ ‖(crossGram y s)⁻¹‖ ≤ (localCoercivity mu sigma)⁻¹ ∧
      ‖crossGram s y - T‖ ≤ 2 * (p : ℝ) * epsilon := by
  have hc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hbase := localReferenceGram_coercive H s mu sigma hmu.le hpositive hgain
  have hcoef : localCoercivity mu sigma ≤ mu * sigma ^ 2 - (p : ℝ) * epsilon := by
    dsimp only [localCoercivity]
    nlinarith
  have hco w := (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖WithLp.toLp 2 w‖)).trans
    (coefficient_coercivity_of_error T _ _ _ hbase hmodel w)
  have hT := coefficient_inverse_of_coercivity T _ hc hco
  have hA := local_observed_domains H hH s y hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  refine ⟨hco, hT.1, hT.2, hA.2.1, hA.2.2.2, ?_⟩
  have heq : crossGram s y - T =
      (crossGram s y - localReferenceGram H s) - (T - localReferenceGram H s) := by abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith [local_pairing_error_norm H hH s y hs he hy])

/-- Original primitive bounds apply uniformly to any selected model
approximating the true Hessian Gram, including a value-corrected model. -/
theorem local_general_model_gradientRelated (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper)
    (he : 0 ≤ epsilon) (heps : epsilon ≤ localStepRadius p mu sigma upper)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v)) (hHnorm : ‖H‖ ≤ upper)
    (hgain : ∀ w : Fin p → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hmodel : ‖T - localReferenceGram H s‖ ≤ (p : ℝ) * epsilon)
    (g : E) (c : ℝ)
    (htrial : modelDirection s y T g ≠ 0 →
      ell * ‖modelDirection s y T g‖ ^ 2 ≤ c ∧ c ≤ trialUpper * ‖modelDirection s y T g‖ ^ 2) :
    GradientRelated (localDescentConstant p mu sigma upper trialUpper)
      (localNormConstant p mu sigma upper ell) g (localModelStepWith s y T g c) := by
  classical
  let C := (localCoercivity mu sigma)⁻¹
  let K := 2 * upper
  have hsmall := localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he heps
  have hdom := local_general_model_domains H hH s y T hs mu sigma epsilon hmu hsigma he
    hpositive hgain hy hmodel hsmall.2.1
  have hC : 0 ≤ C := by dsimp only [C, localCoercivity]; positivity
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hyK (i : Fin p) : ‖y i‖ ≤ K :=
    (image_norm_of_secant_error H s y hs upper epsilon hHnorm hy i).trans (by dsimp only [K]; linarith)
  have hsK (i : Fin p) : ‖s i‖ ≤ 1 := (hs i).le
  have hdefect : C * frameBound p K * ‖crossGram s y - T‖ ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hdom.2.2.2.2.2
      (mul_nonneg hC (by unfold frameBound; positivity))).trans hsmall.2.2
  unfold localModelStepWith
  split
  · rename_i hd
    constructor
    · have hb := modelVirtualCorrection_zero_direction_descent s y T hdom.2.1 g K C
        (localCoercivity mu sigma) hK hC hcoerc hyK hdom.2.2.2.2.1 hdom.1 hdefect hd
      have hc : localDescentConstant p mu sigma upper trialUpper ≤
          localCoercivity mu sigma / (1 + frameBound p K) ^ 2 := min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖g‖)]
    · have hw := modelCoefficients_norm_bound s T 1 C (by norm_num) hC hsK hdom.2.2.1 g
      have hS := synthesis_norm_of_columns s 1 (by norm_num) hsK (modelCoefficients s T g)
      have hb := hS.trans (mul_le_mul_of_nonneg_left hw (by unfold frameBound; positivity))
      have hqpos : 0 ≤ (1 + frameBound p K * C * frameBound p 1) / ell := by unfold frameBound; positivity
      change ‖combine s (modelCoefficients s T g)‖ ≤ _
      dsimp only [localNormConstant]
      nlinarith [mul_nonneg hqpos (norm_nonneg g)]
  · rename_i hd
    have ht := htrial hd
    have hc : 0 < c := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le ht.1
    constructor
    · have hb := (modelTrialStep_descent_bound s y T hdom.2.1 hdom.2.2.2.1 g K C
        (localCoercivity mu sigma) trialUpper c hK hC hcoerc htrialUpper hc
        hsK hyK hdom.2.2.2.2.1 hdom.1 hdefect ht.2).2
      have hcmin : localDescentConstant p mu sigma upper trialUpper ≤
          (blockEnergyConstant (localCoercivity mu sigma) (frameBound p K)
            (trialUpper * (1 + frameBound p 1 * C * frameBound p K) ^ 2))⁻¹ := min_le_left _ _
      nlinarith [mul_le_mul_of_nonneg_right hcmin (sq_nonneg ‖g‖)]
    · exact modelTrialStep_norm_bound s y T hdom.2.2.2.1 g K C c ell hK hC hc hell
        hsK hyK hdom.2.2.1 ht.1

/-- Pair normalization preserves the actual general-model step exactly. -/
theorem localModelStepWith_rescale (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) (hc : IsUnit (diagonal c).det) (g : E) (curvature : ℝ) :
    localModelStepWith (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) g curvature =
      localModelStepWith s y T g curvature := by
  classical
  unfold localModelStepWith
  rw [modelDirection_rescale s y T c hc]
  split
  · exact modelVirtualCorrection_rescale s T c hc g
  · exact modelTrialStep_rescale s y T c hc g curvature

end
end krylov.XR
