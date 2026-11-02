import krylov.XR.LocalGeneralEnergy
import krylov.XR.LocalPrimitiveQuotient

/-!
Article: main_krylov, apG:local(c), general selected-model quotient.
Use: value-corrected models satisfy the same genuine measured-curvature
estimate once their actual Hessian-Gram error is small. The pure window
branch is embedded as a block trial with zero new direction and harmless
positive auxiliary curvature, avoiding any separate denominator assumption.
Source: weighted true Taylor curvature and the actual block-slope identity.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}
local instance generalQuotientDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- The real measured quotient comparison for an arbitrary accurate
selected model, on the positive-energy domain discharged below. -/
theorem measured_model_quotient_bound_with (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Hstar : E →L[ℝ] E) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (hs : ∀ i, ‖s i‖ = 1)
    (hT : IsUnit T.det) (hinv : IsUnit (crossGram y s).det)
    (g x : E) (hcache : G x = g) (c coercivity ell epsilon : ℝ)
    (hc : 0 < c) (hcoercivity : 0 < coercivity) (hell : 0 < ell) (he : 0 ≤ epsilon)
    (hcoerc : ∀ w : Fin p → ℝ, coercivity * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (T *ᵥ w))
    (hcurv : ell * ‖modelDirection s y T g‖ ^ 2 ≤ c)
    (henergy : 0 < modelEnergy s y T g c)
    (hy : ∀ i, ‖y i - Hstar (s i)‖ ≤ epsilon)
    (hmodel : ‖T - localReferenceGram Hstar s‖ ≤ (p : ℝ) * epsilon)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f
      (innerSL ℝ (G (x + t • modelTrialStep s y T g c))) (x + t • modelTrialStep s y T g c))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G
      (H (x + t • modelTrialStep s y T g c)) (x + t • modelTrialStep s y T g c))
    (hH : ContinuousOn (fun t : ℝ => H (x + t • modelTrialStep s y T g c)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (x + t • modelTrialStep s y T g c) - Hstar‖ ≤ epsilon) :
    trialQuotient f x g (modelTrialStep s y T g c) 1 ≤
      max 1 (inner ℝ (Hstar (modelDirection s y T g)) (modelDirection s y T g) / c) +
        (curvatureErrorConstant p / min coercivity ell) * epsilon := by
  let w := modelCoefficients s T g
  let d := modelDirection s y T g
  let t := modelTrialLength s y T g c
  let u := modelTrialStep s y T g c
  let m := min coercivity ell
  let energy := modelEnergy s y T g c
  let ideal := w ⬝ᵥ (T *ᵥ w) + t ^ 2 * inner ℝ (Hstar d) d
  have hm : 0 < m := lt_min hcoercivity hell
  have hden : m * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) ≤ energy := by
    have h₁ := mul_le_mul_of_nonneg_right (min_le_left coercivity ell) (sq_nonneg ‖WithLp.toLp 2 w‖)
    have h₂ := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    have h₃ := mul_le_mul_of_nonneg_right (min_le_right coercivity ell)
      (mul_nonneg (sq_nonneg t) (sq_nonneg ‖d‖))
    dsimp only [energy, modelEnergy, m, w, d, t] at *
    nlinarith [hcoerc (modelCoefficients s T g)]
  have herr := modelTrial_weighted_curvature_error_with H Hstar hHstar s y T hs hinv g x c epsilon
    he hy hmodel hH herror
  dsimp only at herr
  have hC : 0 ≤ curvatureErrorConstant p := by unfold curvatureErrorConstant; positivity
  have hscale : 0 ≤ (curvatureErrorConstant p / m) * epsilon := by positivity
  have hallow : curvatureErrorConstant p * epsilon * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2) ≤
      ((curvatureErrorConstant p / m) * epsilon) * energy := by
    calc
      _ = ((curvatureErrorConstant p / m) * epsilon) *
          (m * (‖WithLp.toLp 2 w‖ ^ 2 + t ^ 2 * ‖d‖ ^ 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hden hscale
  have hnum : weightedCurvature H x u ≤ ideal +
      ((curvatureErrorConstant p / m) * epsilon) * energy := by
    have hh := (abs_le.mp herr).2
    change weightedCurvature H x u - ideal ≤ _ at hh
    linarith
  have hquot := div_le_div_of_nonneg_right hnum henergy.le
  have hdist : (ideal + ((curvatureErrorConstant p / m) * epsilon) * energy) / energy =
      ideal / energy + (curvatureErrorConstant p / m) * epsilon := by
    field_simp [show energy ≠ 0 from henergy.ne', hm.ne']
  rw [hdist] at hquot
  have hratio := block_curvature_ratio (w ⬝ᵥ (T *ᵥ w)) t (inner ℝ (Hstar d) d) c
    ((mul_nonneg hcoercivity.le (sq_nonneg _)).trans (hcoerc w)) hc henergy
  rw [trialQuotient_model_energy f G H s y T hT g x hcache c hc hF hG hH]
  change weightedCurvature H x u / energy ≤ _
  change ideal / energy ≤ _ at hratio
  nlinarith

/-- Genuine primitive data derive the positive denominator and complete
measured-quotient bound for any selected observed model, including its
full-window and zero-direction branches. -/
theorem primitive_local_model_quotient_with (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Hstar : E →L[ℝ] E) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ localStepRadius p mu sigma upper)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Hstar v)) (hHnorm : ‖Hstar‖ ≤ upper)
    (hgain : ∀ w : Fin p → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - Hstar (s i)‖ ≤ epsilon)
    (hmodel : ‖T - localReferenceGram Hstar s‖ ≤ (p : ℝ) * epsilon)
    (g x : E) (hg : g ≠ 0) (hcache : G x = g) (c : ℝ)
    (htrial : modelDirection s y T g ≠ 0 →
      ell * ‖modelDirection s y T g‖ ^ 2 ≤ c ∧ c ≤ trialUpper * ‖modelDirection s y T g‖ ^ 2)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f
      (innerSL ℝ (G (x + t • localModelStepWith s y T g c))) (x + t • localModelStepWith s y T g c))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G
      (H (x + t • localModelStepWith s y T g c)) (x + t • localModelStepWith s y T g c))
    (hH : ContinuousOn (fun t : ℝ => H (x + t • localModelStepWith s y T g c)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (x + t • localModelStepWith s y T g c) - Hstar‖ ≤ epsilon) :
    let d := modelDirection s y T g
    trialQuotient f x g (localModelStepWith s y T g c) 1 ≤
      (if d = 0 then 1 else max 1 (inner ℝ (Hstar d) d / c)) +
        localQuotientConstant p mu sigma ell * epsilon := by
  classical
  let d := modelDirection s y T g
  let c' : ℝ := if d = 0 then 1 else c
  have hsmall := localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he heps
  have hdom := local_general_model_domains Hstar hHstar s y T hs mu sigma epsilon hmu hsigma he
    hpositive hgain hy hmodel hsmall.2.1
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hstep := local_general_model_gradientRelated Hstar hHstar s y T hs mu sigma upper ell trialUpper
    epsilon hmu hsigma hupper hell htrialUpper he heps hpositive hHnorm hgain hy hmodel g c htrial
  have hslope : inner ℝ g (localModelStepWith s y T g c) < 0 := hstep.1.trans_lt (by
    have hp := mul_pos (localDescentConstant_pos (p := p) mu sigma upper trialUpper hmu hsigma hupper)
      (sq_pos_of_pos (norm_pos_iff.mpr hg))
    nlinarith)
  have hc' : 0 < c' := by
    dsimp only [c']
    split_ifs with hd
    · norm_num
    · exact (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le (htrial hd).1
  have hu : localModelStepWith s y T g c = modelTrialStep s y T g c' := by
    by_cases hd : d = 0
    · simp only [localModelStepWith, show modelDirection s y T g = 0 from hd, ite_true,
        modelTrialStep, smul_zero, add_zero]
    · simp only [localModelStepWith, show modelDirection s y T g ≠ 0 from hd, ite_false, c', hd]
  have hcurv : ell * ‖d‖ ^ 2 ≤ c' := by
    by_cases hd : d = 0
    · simp only [hd, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, c', ite_true]
      norm_num
    · simpa only [c', hd, ite_false] using (htrial hd).1
  have henergy : 0 < modelEnergy s y T g c' := by
    rw [modelEnergy_eq_neg_slope s y T hdom.2.1 g c' hc']
    rw [hu] at hslope
    linarith
  have hq := measured_model_quotient_bound_with f G H Hstar hHstar s y T hs hdom.2.1 hdom.2.2.2.1
    g x hcache c' (localCoercivity mu sigma) ell epsilon hc' hcoerc hell he hdom.1 hcurv henergy hy hmodel
    (by simpa only [hu] using hF) (by simpa only [hu] using hG)
    (by simpa only [hu] using hH) (by simpa only [hu] using herror)
  dsimp only
  rw [hu]
  change trialQuotient f x g (modelTrialStep s y T g c') 1 ≤
    (if d = 0 then 1 else max 1 (inner ℝ (Hstar d) d / c)) +
      localQuotientConstant p mu sigma ell * epsilon
  change trialQuotient f x g (modelTrialStep s y T g c') 1 ≤
    max 1 (inner ℝ (Hstar d) d / c') +
      (curvatureErrorConstant p / min (localCoercivity mu sigma) ell) * epsilon at hq
  have hm := mul_le_mul_of_nonneg_right (le_max_right
    (((p : ℝ) + (frameBound p 1) ^ 2) / localCoercivity mu sigma)
    (curvatureErrorConstant p / min (localCoercivity mu sigma) ell)) he
  by_cases hd : d = 0
  · simp only [hd, c', ite_true, map_zero, inner_zero_left, zero_div, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)] at hq ⊢
    exact hq.trans (by dsimp only [localQuotientConstant]; linarith)
  · simp only [hd, c', ite_false] at hq ⊢
    exact hq.trans (by dsimp only [localQuotientConstant]; linarith)

end
end krylov.XR
