import krylov.XR.LocalSelectedModel

/-!
Article: main_krylov, apG:local(c), literal selected-model quotient.
Use: transfer the genuine general-model Taylor estimate through exact
pair normalization to the raw direction computed by ModelStep. It applies
to the ordinary and value-corrected branches with the same constants.
Source: true observed coefficient solves and weighted scalar Taylor energy.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local instance selectedQuotientDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Genuine primitive data give the actual measured quotient estimate for
the literal selected-model direction, in unnormalized physical coordinates. -/
theorem algorithmModel_selected_quotient (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (algorithmModel P S).pairs.length ≠ 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Hstar : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Hstar v)) (hHnorm : ‖Hstar‖ ≤ upper)
    (hs : ∀ i, storedSteps (algorithmModel P S).pairs i ≠ 0)
    (hgain : ∀ w : Fin (algorithmModel P S).pairs.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps (algorithmModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (algorithmModel P S).pairs i - Hstar (storedSteps (algorithmModel P S).pairs i)‖ ≤
      epsilon * ‖storedSteps (algorithmModel P S).pairs i‖)
    (hmodel : ‖rescaleModel (selectedModel P (algorithmModel P S).pairs)
      (fun i => ‖storedSteps (algorithmModel P S).pairs i‖⁻¹) -
      localReferenceGram Hstar (krylov.Convergence.unitWindow (storedSteps (algorithmModel P S).pairs))‖ ≤
        ((algorithmModel P S).pairs.length : ℝ) * epsilon)
    (hg : S.gradient ≠ 0) (hcache : G S.point = S.gradient)
    (htrial : algorithmSelectedDirection P S ≠ 0 →
      ell * ‖algorithmSelectedDirection P S‖ ^ 2 ≤ algorithmComputedCurvature P S ∧
        algorithmComputedCurvature P S ≤ trialUpper * ‖algorithmSelectedDirection P S‖ ^ 2)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f
      (innerSL ℝ (G (S.point + t • (algorithmModel P S).direction))) (S.point + t • (algorithmModel P S).direction))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G
      (H (S.point + t • (algorithmModel P S).direction)) (S.point + t • (algorithmModel P S).direction))
    (hH : ContinuousOn (fun t : ℝ => H (S.point + t • (algorithmModel P S).direction)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (S.point + t • (algorithmModel P S).direction) - Hstar‖ ≤ epsilon) :
    let d := algorithmSelectedDirection P S
    trialQuotient f S.point S.gradient (algorithmModel P S).direction 1 ≤
      (if d = 0 then 1 else max 1 (inner ℝ (Hstar d) d / algorithmComputedCurvature P S)) +
        dimensionQuotientConstant n mu sigma ell * epsilon := by
  let M := algorithmModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := selectedModel P M.pairs
  let sn := krylov.Convergence.unitWindow s
  let yn := krylov.Convergence.unitWindowImages s y
  let c := fun i => ‖s i‖⁻¹
  have hc := krylov.Convergence.unitWindow_diagonal_unit s hs
  have hlen : M.pairs.length ≤ n := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hep := heps.trans (prefixMinimum_le _ n M.pairs.length hlen)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he hep).2.1
  have hdom := local_raw_window_domains Hstar hHstar s y hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  have hdir : modelDirection sn yn (rescaleModel T c) S.gradient = algorithmSelectedDirection P S :=
    modelDirection_rescale s y T c hc S.gradient
  have hu : localModelStepWith sn yn (rescaleModel T c) S.gradient (algorithmComputedCurvature P S) = M.direction := by
    change localModelStepWith (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) S.gradient _ = M.direction
    rw [localModelStepWith_rescale s y T c hc]
    exact (algorithmModel_direction_eq_selected_local P S hp hdom.2.2.1).symm
  have hq := primitive_local_model_quotient_with f G H Hstar hHstar sn yn (rescaleModel T c)
    (krylov.Convergence.unitWindow_norm s hs) mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he hep hpositive hHnorm hgain
    (unitWindow_reference_error Hstar s y hs epsilon hy) hmodel S.gradient S.point hg hcache (algorithmComputedCurvature P S)
    (by rw [hdir]; exact htrial)
    (by simpa only [hu] using hF) (by simpa only [hu] using hG)
    (by simpa only [hu] using hH) (by simpa only [hu] using herror)
  dsimp only at hq ⊢
  rw [hu, hdir] at hq
  have hm := mul_le_mul_of_nonneg_right
    (le_prefixMaximum (fun p => localQuotientConstant p mu sigma ell) n M.pairs.length hlen) he
  by_cases hd : algorithmSelectedDirection P S = 0
  · simp only [ite_eq_left hd] at hq ⊢
    exact hq.trans (add_le_add le_rfl hm)
  · simp only [ite_eq_right hd] at hq ⊢
    exact hq.trans (add_le_add le_rfl hm)

/-- The strict G3 allowance absorbs the genuine measured-curvature error
in either the pure-window or the nonzero new-direction branch. -/
theorem quotient_acceptance_from_margin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →L[ℝ] E) (d : E) (q c C epsilon armijo eta ell : ℝ) (hell : 0 < ell)
    (hquot : q ≤ (if d = 0 then 1 else max 1 (inner ℝ (H d) d / c)) + C * epsilon)
    (hcurv : d ≠ 0 → ell * ‖d‖ ^ 2 ≤ c ∧ inner ℝ (H d) d ≤ (2 * (1 - armijo) - eta) * c)
    (hallow : C * epsilon ≤ min (1 - 2 * armijo) eta) : q ≤ 2 * (1 - armijo) := by
  have hm₁ := min_le_left (1 - 2 * armijo) eta
  have hm₂ := min_le_right (1 - 2 * armijo) eta
  by_cases hd : d = 0
  · rw [ite_eq_left hd] at hquot
    linarith
  · have ht := hcurv hd
    have hc : 0 < c := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hd))).trans_le ht.1
    have hr : inner ℝ (H d) d / c ≤ 2 * (1 - armijo) - eta := (div_le_iff₀ hc).2 ht.2
    rw [ite_eq_right hd] at hquot
    rcases max_cases (1 : ℝ) (inner ℝ (H d) d / c) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hquot
      linarith
    · rw [he] at hquot
      linarith

end
end krylov.XR
