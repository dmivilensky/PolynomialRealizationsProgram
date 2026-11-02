import krylov.XR.LocalDimensionConstants
import krylov.XR.LocalWindowQuotient

/-!
Article: main_krylov, apG:local(c), primitive measured-quotient theorem.
Use: discharge every inverse/model-energy domain from genuine source
secants, Hessian positivity and normalized independence. In particular the
actual positive denominator is derived from the proved model descent;
it is not a query or execution field. Source: actual weighted Taylor
identity and the preceding primitive local model-step bounds.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}
local instance primitiveQuotientDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- One fixed-size measured quotient constant covers both genuine model
branches, including the pure window correction. -/
def localQuotientConstant (p : ℕ) (mu sigma ell : ℝ) : ℝ :=
  max (((p : ℝ) + (frameBound p 1) ^ 2) / localCoercivity mu sigma)
    (curvatureErrorConstant p / min (localCoercivity mu sigma) ell)

/-- Original dependence on n can be fixed before all actual window sizes. -/
def dimensionQuotientConstant (n : ℕ) (mu sigma ell : ℝ) : ℝ :=
  prefixMaximum (fun p => localQuotientConstant p mu sigma ell) n

/-- Actual local C²/observed-pair data imply the genuine measured
quotient estimate without a positive-energy or inverse-domain premise. -/
theorem primitive_local_model_quotient (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Hstar : E →L[ℝ] E) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ localStepRadius p mu sigma upper)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Hstar v)) (hHnorm : ‖Hstar‖ ≤ upper)
    (hgain : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - Hstar (s i)‖ ≤ epsilon) (g x : E) (hg : g ≠ 0)
    (hcache : G x = g) (c : ℝ)
    (htrial : modelDirection s y (latest (crossGram s y)) g ≠ 0 →
      ell * ‖modelDirection s y (latest (crossGram s y)) g‖ ^ 2 ≤ c ∧
        c ≤ trialUpper * ‖modelDirection s y (latest (crossGram s y)) g‖ ^ 2)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt f (innerSL ℝ (G (x + t • localModelStep s y g c))) (x + t • localModelStep s y g c))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt G (H (x + t • localModelStep s y g c)) (x + t • localModelStep s y g c))
    (hH : ContinuousOn (fun t : ℝ => H (x + t • localModelStep s y g c)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (x + t • localModelStep s y g c) - Hstar‖ ≤ epsilon) :
    let d := modelDirection s y (latest (crossGram s y)) g
    trialQuotient f x g (localModelStep s y g c) 1 ≤
      (if d = 0 then 1 else max 1 (inner ℝ (Hstar d) d / c)) +
        localQuotientConstant p mu sigma ell * epsilon := by
  classical
  let T := latest (crossGram s y)
  let d := modelDirection s y T g
  have hsmall := localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he heps
  have hdom := local_observed_domains Hstar hHstar s y hs mu sigma epsilon hmu hsigma he
    hpositive hgain hy hsmall.2.1
  have hco := (local_observed_coercivity Hstar hHstar s y hs mu sigma epsilon hmu he
    hpositive hgain hy hsmall.2.1).1
  have hT : IsUnit T.det := isUnit_iff_ne_zero.mpr hdom.1.det_pos.ne'
  have hcoercivity : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hstep := local_model_step_gradientRelated Hstar hHstar s y hs mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he heps hpositive hHnorm hgain hy g c htrial
  have hslope : inner ℝ g (localModelStep s y g c) < 0 := hstep.1.trans_lt (by
    have hp := mul_pos (localDescentConstant_pos (p := p) mu sigma upper trialUpper hmu hsigma hupper)
      (sq_pos_of_pos (norm_pos_iff.mpr hg))
    nlinarith)
  by_cases hd : d = 0
  · have hu : localModelStep s y g c = modelVirtualCorrection s T g := by
      simp only [localModelStep, show modelDirection s y (latest (crossGram s y)) g = 0 from hd, ite_true]
      rfl
    rw [hu, modelVirtualCorrection_slope s T hT g] at hslope
    have henergy : 0 < modelCoefficients s T g ⬝ᵥ (T *ᵥ modelCoefficients s T g) := by linarith
    have hbound := measured_window_quotient_bound f G H Hstar hHstar s y hs hT g x hcache
      (localCoercivity mu sigma) epsilon hcoercivity he hco henergy hy
      (by simpa only [hu] using hF) (by simpa only [hu] using hG)
      (by simpa only [hu] using hH) (by simpa only [hu] using herror)
    dsimp only
    rw [hu, ite_eq_left hd]
    have hm := mul_le_mul_of_nonneg_right (le_max_left
      (((p : ℝ) + (frameBound p 1) ^ 2) / localCoercivity mu sigma)
      (curvatureErrorConstant p / min (localCoercivity mu sigma) ell)) he
    exact hbound.trans (by dsimp only [localQuotientConstant]; linarith)
  · have hu : localModelStep s y g c = modelTrialStep s y T g c := by
      simp only [localModelStep, show modelDirection s y (latest (crossGram s y)) g ≠ 0 from hd, ite_false]
      rfl
    have hc : 0 < c := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le (htrial hd).1
    have henergy : 0 < modelEnergy s y T g c := by
      rw [modelEnergy_eq_neg_slope s y T hT g c hc]
      rw [hu] at hslope
      linarith
    have hbound := measured_model_quotient_bound f G H Hstar hHstar s y hs hT hdom.2.1 g x hcache c
      (localCoercivity mu sigma) ell epsilon hc hcoercivity hell he hco (htrial hd).1 henergy hy
      (by simpa only [hu] using hF) (by simpa only [hu] using hG)
      (by simpa only [hu] using hH) (by simpa only [hu] using herror)
    dsimp only at hbound ⊢
    rw [hu, ite_eq_right hd]
    have hm := mul_le_mul_of_nonneg_right (le_max_right
      (((p : ℝ) + (frameBound p 1) ^ 2) / localCoercivity mu sigma)
      (curvatureErrorConstant p / min (localCoercivity mu sigma) ell)) he
    exact hbound.trans (by dsimp only [localQuotientConstant]; linarith)

end
end krylov.XR
