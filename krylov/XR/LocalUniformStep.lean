import krylov.XR.LocalStepBounds
import krylov.XR.Safeguard

/-!
Article: main_krylov, apG:local(b), primitive uniform model-step bounds.
Use: instantiate all coefficient, direction and slope estimates from the
original actual secant errors, true Hessian bounds and normalized column
independence. No descent, angle or accepted-branch condition is assumed.
Source: the proved rectangular coefficient geometry and block energy.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- A source-only radius sufficient for the real coefficient domains and
the small computed-slope-defect allowance. -/
def localStepRadius (p : ℕ) (mu sigma upper : ℝ) : ℝ :=
  min upper (min (mu * sigma ^ 2 / (4 * ((p : ℝ) + 1)))
    (1 / (2 * ((p : ℝ) + 1) * (localCoercivity mu sigma)⁻¹ * frameBound p (2 * upper) + 1)))

/-- The radius is genuinely positive under the primitive spectral and
independence assumptions. -/
theorem localStepRadius_pos (mu sigma upper : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper) :
    0 < localStepRadius p mu sigma upper := by
  unfold localStepRadius localCoercivity frameBound
  positivity

/-- The source radius supplies both actual coefficient smallness tests. -/
theorem localStepRadius_small (mu sigma upper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (he : 0 ≤ epsilon) (heps : epsilon ≤ localStepRadius p mu sigma upper) :
    epsilon ≤ upper ∧ (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4 ∧
      (localCoercivity mu sigma)⁻¹ * frameBound p (2 * upper) *
        (2 * (p : ℝ) * epsilon) ≤ 1 := by
  have hC : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hB : 0 ≤ frameBound p (2 * upper) := by unfold frameBound; positivity
  have hden : 0 < 2 * ((p : ℝ) + 1) * (localCoercivity mu sigma)⁻¹ *
      frameBound p (2 * upper) + 1 := by positivity
  have h₁ := heps.trans (min_le_left _ _)
  have h₂ := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h₂' := (le_div_iff₀ (by positivity : 0 < 4 * ((p : ℝ) + 1))).mp h₂
  have h₃' := (le_div_iff₀ hden).mp h₃
  refine ⟨h₁, ?_, ?_⟩
  · nlinarith
  · have hnonneg : 0 ≤ (localCoercivity mu sigma)⁻¹ * frameBound p (2 * upper) :=
      mul_nonneg (inv_nonneg.mpr hC.le) hB
    nlinarith [mul_nonneg he hnonneg]

/-- Constants for the primitive uniform step estimate. Their dependence
is only on the stated dimension/spectral/independence/trial bounds. -/
def localDescentConstant (p : ℕ) (mu sigma upper trialUpper : ℝ) : ℝ :=
  let C := (localCoercivity mu sigma)⁻¹
  let B := frameBound p (2 * upper)
  let D := 1 + frameBound p 1 * C * B
  min (blockEnergyConstant (localCoercivity mu sigma) B (trialUpper * D ^ 2))⁻¹
    (localCoercivity mu sigma / (1 + B) ^ 2)

/-- Uniform physical model-step norm constant. -/
def localNormConstant (p : ℕ) (mu sigma upper ell : ℝ) : ℝ :=
  let C := (localCoercivity mu sigma)⁻¹
  frameBound p 1 * C * frameBound p 1 +
    (1 + frameBound p (2 * upper) * C * frameBound p 1) / ell

/-- The uniform descent constant is strictly positive. -/
theorem localDescentConstant_pos (mu sigma upper trialUpper : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper) :
    0 < localDescentConstant p mu sigma upper trialUpper := by
  have hc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hB : 0 ≤ frameBound p (2 * upper) := by unfold frameBound; positivity
  unfold localDescentConstant
  dsimp only
  apply lt_min
  · apply inv_pos.mpr
    apply lt_of_lt_of_le _ (le_max_left _ _)
    exact div_pos (by positivity) hc
  · exact div_pos hc (sq_pos_of_pos (by positivity))

/-- The physical norm constant is strictly positive. -/
theorem localNormConstant_pos (mu sigma upper ell : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper) (hell : 0 < ell) :
    0 < localNormConstant p mu sigma upper ell := by
  unfold localNormConstant localCoercivity frameBound
  positivity

/-- The literal zero-direction choice is the window move; otherwise it is
the computed window-plus-new-direction model trial. -/
def localModelStep (s y : Fin p → E) (g : E) (c : ℝ) : E := by
  classical
  let T := latest (crossGram s y)
  exact if modelDirection s y T g = 0 then modelVirtualCorrection s T g
    else modelTrialStep s y T g c

/-- The original primitive local source assumptions imply uniform descent
and step-norm bounds for every actual computed model step. -/
theorem local_model_step_gradientRelated (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper)
    (he : 0 ≤ epsilon) (heps : epsilon ≤ localStepRadius p mu sigma upper)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v)) (hHnorm : ‖H‖ ≤ upper)
    (hindependent : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) (g : E) (c : ℝ)
    (htrial : modelDirection s y (latest (crossGram s y)) g ≠ 0 →
      ell * ‖modelDirection s y (latest (crossGram s y)) g‖ ^ 2 ≤ c ∧
        c ≤ trialUpper * ‖modelDirection s y (latest (crossGram s y)) g‖ ^ 2) :
    GradientRelated (localDescentConstant p mu sigma upper trialUpper)
      (localNormConstant p mu sigma upper ell) g (localModelStep s y g c) := by
  classical
  let T := latest (crossGram s y)
  let C := (localCoercivity mu sigma)⁻¹
  let K := 2 * upper
  have hsmall := localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he heps
  have hdom := local_observed_domains H hH s y hs mu sigma epsilon hmu hsigma he
    hpositive hindependent hy hsmall.2.1
  have hco := (local_observed_coercivity H hH s y hs mu sigma epsilon hmu he
    hpositive hindependent hy hsmall.2.1).1
  have hC : 0 ≤ C := by dsimp only [C, localCoercivity]; positivity
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hyK (i : Fin p) : ‖y i‖ ≤ K :=
    (image_norm_of_secant_error H s y hs upper epsilon hHnorm hy i).trans (by dsimp only [K]; linarith)
  have hsK (i : Fin p) : ‖s i‖ ≤ 1 := (hs i).le
  have hT : IsUnit T.det := isUnit_iff_ne_zero.mpr hdom.1.det_pos.ne'
  have hdefect : C * frameBound p K * ‖crossGram s y - T‖ ≤ 1 := by
    have hn := local_pairing_latest_gap H hH s y hs he hy
    exact (mul_le_mul_of_nonneg_left hn
      (mul_nonneg hC (by unfold frameBound; positivity))).trans hsmall.2.2
  unfold localModelStep
  dsimp only
  split
  · rename_i hd
    constructor
    · have hb := modelVirtualCorrection_zero_direction_descent s y T hT g K C
        (localCoercivity mu sigma) hK hC hcoerc hyK hdom.2.2.2 hco hdefect hd
      have hc : localDescentConstant p mu sigma upper trialUpper ≤
          localCoercivity mu sigma / (1 + frameBound p K) ^ 2 := min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖g‖)]
    · have hw := modelCoefficients_norm_bound s T 1 C (by norm_num) hC hsK hdom.2.2.1 g
      have hS := synthesis_norm_of_columns s 1 (by norm_num) hsK (modelCoefficients s T g)
      have hb := hS.trans (mul_le_mul_of_nonneg_left hw (by unfold frameBound; positivity))
      have hqpos : 0 ≤ (1 + frameBound p K * C * frameBound p 1) / ell := by
        unfold frameBound
        positivity
      change ‖combine s (modelCoefficients s T g)‖ ≤ _
      dsimp only [localNormConstant]
      nlinarith [mul_nonneg hqpos (norm_nonneg g)]
  · rename_i hd
    have ht := htrial hd
    have hc : 0 < c :=
      (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le ht.1
    constructor
    · have hb := (modelTrialStep_descent_bound s y T hT hdom.2.1 g K C
        (localCoercivity mu sigma) trialUpper c hK hC hcoerc htrialUpper hc
        hsK hyK hdom.2.2.2 hco hdefect ht.2).2
      have hcmin : localDescentConstant p mu sigma upper trialUpper ≤
          (blockEnergyConstant (localCoercivity mu sigma) (frameBound p K)
            (trialUpper * (1 + frameBound p 1 * C * frameBound p K) ^ 2))⁻¹ := min_le_left _ _
      nlinarith [mul_le_mul_of_nonneg_right hcmin (sq_nonneg ‖g‖)]
    · exact modelTrialStep_norm_bound s y T hdom.2.1 g K C c ell hK hC hc hell
        hsK hyK hdom.2.2.1 ht.1

end
end krylov.XR
