import krylov.XR.LocalModelStep
import krylov.XR.LocalPrimitiveQuotient

/-!
Article: main_krylov, thm:grow and apG:local(c), actual unit acceptance.
Use: turn the primitive true Taylor quotient estimate and G3 into the
literal Armijo branch decision for unnormalized observed pairs. The
positive denominator and all inverse domains are derived. Source: exact
pair normalization and the measured Hessian remainder.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Primitive local secants and genuine function derivatives force the
actual raw ModelStep to pass the unit Armijo test. -/
theorem algorithmModel_unit_accepted (P : Parameters) (hoff : P.valuesEnabled = false)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (algorithmModel P S).pairs.length ≠ 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Hstar : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hHstar : Hstar.toLinearMap.IsSymmetric)
    (mu sigma upper ell trialUpper epsilon eta : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon) (_heta : 0 < eta)
    (_harmijo : P.armijo < 1 / 2)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hallow : dimensionQuotientConstant n mu sigma ell * epsilon ≤ min (1 - 2 * P.armijo) eta)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Hstar v)) (hHnorm : ‖Hstar‖ ≤ upper)
    (hs : ∀ i, storedSteps (algorithmModel P S).pairs i ≠ 0)
    (hgain : ∀ w : Fin (algorithmModel P S).pairs.length → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps (algorithmModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (algorithmModel P S).pairs i - Hstar (storedSteps (algorithmModel P S).pairs i)‖ ≤
      epsilon * ‖storedSteps (algorithmModel P S).pairs i‖)
    (hg : S.gradient ≠ 0) (hcache : G S.point = S.gradient)
    (htrial : modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
        (storedModel (algorithmModel P S).pairs) S.gradient ≠ 0 →
      ell * ‖modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
        (storedModel (algorithmModel P S).pairs) S.gradient‖ ^ 2 ≤ algorithmComputedCurvature P S ∧
      algorithmComputedCurvature P S ≤ trialUpper *
        ‖modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
          (storedModel (algorithmModel P S).pairs) S.gradient‖ ^ 2 ∧
      inner ℝ (Hstar (modelDirection (storedSteps (algorithmModel P S).pairs)
        (storedImages (algorithmModel P S).pairs) (storedModel (algorithmModel P S).pairs) S.gradient))
        (modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
          (storedModel (algorithmModel P S).pairs) S.gradient) ≤
        (2 * (1 - P.armijo) - eta) * algorithmComputedCurvature P S)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f
      (innerSL ℝ (G (S.point + t • (algorithmModel P S).direction))) (S.point + t • (algorithmModel P S).direction))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G
      (H (S.point + t • (algorithmModel P S).direction)) (S.point + t • (algorithmModel P S).direction))
    (hH : ContinuousOn (fun t : ℝ => H (S.point + t • (algorithmModel P S).direction)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H (S.point + t • (algorithmModel P S).direction) - Hstar‖ ≤ epsilon) :
    Accepted f P.armijo S.point S.gradient (algorithmModel P S).direction 1 := by
  classical
  let M := algorithmModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let sn := krylov.Convergence.unitWindow s
  let yn := krylov.Convergence.unitWindowImages s y
  let d := modelDirection s y (storedModel M.pairs) S.gradient
  let c := algorithmComputedCurvature P S
  have hlen : M.pairs.length ≤ n := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hep := heps.trans (prefixMinimum_le _ n M.pairs.length hlen)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he hep).2.1
  have hdom := local_raw_window_domains Hstar hHstar s y hs mu sigma epsilon hmu hsigma he
    hpositive hgain hy hsmall
  have hdir : modelDirection sn yn (latest (crossGram sn yn)) S.gradient = d := by
    rw [show latest (crossGram sn yn) = rescaleModel (latest (crossGram s y)) (fun i => ‖s i‖⁻¹) from
      krylov.Convergence.ss1Model_rescale s y _]
    exact modelDirection_rescale s y _ _ (krylov.Convergence.unitWindow_diagonal_unit s hs) _
  have hu : localModelStep sn yn S.gradient c = M.direction := by
    change localModelStep (rescaleWindow s (fun i => ‖s i‖⁻¹))
      (rescaleWindow y (fun i => ‖s i‖⁻¹)) S.gradient c = M.direction
    rw [localModelStep_rescale s y _ (krylov.Convergence.unitWindow_diagonal_unit s hs)]
    exact (algorithmModel_direction_eq_local P hoff S hp hdom.2.2.1).symm
  have hq := primitive_local_model_quotient f G H Hstar hHstar sn yn
    (krylov.Convergence.unitWindow_norm s hs) mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he hep hpositive hHnorm hgain
    (unitWindow_reference_error Hstar s y hs epsilon hy) S.gradient S.point hg hcache c
    (by rw [hdir]; intro hd; have h := htrial hd; exact ⟨h.1, h.2.1⟩)
    (by simpa only [hu] using hF) (by simpa only [hu] using hG)
    (by simpa only [hu] using hH) (by simpa only [hu] using herror)
  dsimp only at hq
  rw [hu, hdir] at hq
  have hconst : localQuotientConstant M.pairs.length mu sigma ell * epsilon ≤
      min (1 - 2 * P.armijo) eta :=
    (mul_le_mul_of_nonneg_right (le_prefixMaximum _ n M.pairs.length hlen) he).trans hallow
  have hm₁ := min_le_left (1 - 2 * P.armijo) eta
  have hm₂ := min_le_right (1 - 2 * P.armijo) eta
  change trialQuotient f S.point S.gradient M.direction 1 ≤ _
  by_cases hd : d = 0
  · rw [ite_eq_left hd] at hq
    linarith
  · have ht := htrial hd
    have hc : 0 < c := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le ht.1
    have hratio : inner ℝ (Hstar d) d / c ≤ 2 * (1 - P.armijo) - eta :=
      (div_le_iff₀ hc).2 ht.2.2
    rw [ite_eq_right hd] at hq
    rcases max_cases (1 : ℝ) (inner ℝ (Hstar d) d / c) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq] at hq
      linarith
    · rw [heq] at hq
      linarith

end
end krylov.XR
