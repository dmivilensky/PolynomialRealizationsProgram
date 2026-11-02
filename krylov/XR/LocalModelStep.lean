import krylov.XR.LocalModelActivation
import krylov.XR.QuadraticTrial

/-!
Article: main_krylov, thm:grow and apG:local(b), actual raw model step.
Use: connect the literal data-only executor, including its full-window
branch, to the primitive physical local estimates after exact pair
normalization. No descent, output bound or inactive-safeguard field is
assumed. Source: the genuine computed inverse solves and source-only bounds.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual observed trial curvature used by the partial-window branch.
The interval always uses the original latest model, as in alg:xr. -/
def algorithmComputedCurvature (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) : ℝ :=
  let M := algorithmModel P S
  observedTrialCurvature P M.pairs (storedModel M.pairs)
    (modelDirection (storedSteps M.pairs) (storedImages M.pairs) (selectedModel P M.pairs) S.gradient)
    (M.bounds.getD (M.fallbackCurvature, M.fallbackCurvature))

/-- With F disabled the selected observed model is exactly the original
latest-information matrix, independently of every measured value. -/
theorem selectedModel_values_off (P : Parameters) (hoff : P.valuesEnabled = false)
    (W : List (PairObservation (EuclideanSpace ℝ (Fin n)))) : selectedModel P W = storedModel W := by
  classical
  simp only [selectedModel, hoff, Bool.false_eq_true, false_and, ite_false]

/-- The literal full-window branch agrees with the computed zero-direction
local model step; the zero direction is derived from the actual inverse
domain and full physical rank, not assumed as a branch certificate. -/
theorem algorithmModel_direction_eq_local (P : Parameters) (hoff : P.valuesEnabled = false)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (algorithmModel P S).pairs.length ≠ 0)
    (hinv : IsUnit (crossGram (storedImages (algorithmModel P S).pairs)
      (storedSteps (algorithmModel P S).pairs)).det) :
    (algorithmModel P S).direction = localModelStep (storedSteps (algorithmModel P S).pairs)
      (storedImages (algorithmModel P S).pairs) S.gradient (algorithmComputedCurvature P S) := by
  classical
  let M := algorithmModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := storedModel M.pairs
  let d := modelDirection s y T S.gradient
  change M.direction = localModelStep s y S.gradient (algorithmComputedCurvature P S)
  have hselected := selectedModel_values_off P hoff M.pairs
  have hfull (hcount : M.pairs.length = n) : d = 0 := by
    have hspan : Submodule.span ℝ (range s) = ⊤ :=
      (algorithmModel_independent P S).span_eq_top_of_card_eq_finrank' (by
        rw [Fintype.card_fin, finrank_euclideanSpace_fin]
        exact hcount)
    exact modelDirection_zero_of_full_span s y T hinv hspan S.gradient
  have hdecomp := algorithmModel_direction_decomposition P S hp
  rw [hselected] at hdecomp
  change M.direction = modelVirtualCorrection s T S.gradient + algorithmTrialParameter P S • d at hdecomp
  by_cases hd : d = 0
  · rw [hd, smul_zero, add_zero] at hdecomp
    rw [hdecomp]
    unfold localModelStep
    dsimp only
    rw [ite_eq_left (show modelDirection s y (latest (crossGram s y)) S.gradient = 0 from hd)]
    rfl

  · have hnotfull : M.pairs.length ≠ n := fun h => hd (hfull h)
    have hparameter : algorithmTrialParameter P S =
        modelTrialLength s y T S.gradient (algorithmComputedCurvature P S) := by
      change (if M.pairs.length = 0 then
        (match M.bounds with | none => S.initialStep | some b => 2 / (b.1 + b.2))
        else if M.pairs.length = n ∨ modelDirection s y (selectedModel P M.pairs) S.gradient = 0 then 0
        else modelTrialLength s y (selectedModel P M.pairs) S.gradient (algorithmComputedCurvature P S)) = _
      rw [ite_eq_right hp, hselected, ite_eq_right (not_or.mpr ⟨hnotfull, hd⟩)]
    rw [hdecomp, hparameter]
    unfold localModelStep
    dsimp only
    rw [ite_eq_right (show modelDirection s y (latest (crossGram s y)) S.gradient ≠ 0 from hd)]
    rfl

/-- On its genuine observed inverse domain a nonzero new direction of a
nonempty model can only occur before full physical dimension. -/
theorem algorithmModel_partial_of_direction_ne_zero (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hinv : IsUnit (crossGram (storedImages (algorithmModel P S).pairs)
      (storedSteps (algorithmModel P S).pairs)).det)
    (hd : modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
      (storedModel (algorithmModel P S).pairs) S.gradient ≠ 0) :
    (algorithmModel P S).pairs.length < n := by
  have hlen := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hnotfull : (algorithmModel P S).pairs.length ≠ n := by
    intro he
    have hspan := (algorithmModel_independent P S).span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
      exact he)
    exact hd (modelDirection_zero_of_full_span _ _ _ hinv hspan _)
  omega

/-- The actual raw ModelStep has uniform primitive local descent and norm
bounds in original unnormalized physical coordinates. -/
theorem algorithmModel_local_gradientRelated (P : Parameters) (hoff : P.valuesEnabled = false)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (algorithmModel P S).pairs.length ≠ 0)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : H.toLinearMap.IsSymmetric)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v)) (hHnorm : ‖H‖ ≤ upper)
    (hs : ∀ i, storedSteps (algorithmModel P S).pairs i ≠ 0)
    (hgain : ∀ w : Fin (algorithmModel P S).pairs.length → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps (algorithmModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (algorithmModel P S).pairs i - H (storedSteps (algorithmModel P S).pairs i)‖ ≤
      epsilon * ‖storedSteps (algorithmModel P S).pairs i‖)
    (htrial : modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
        (storedModel (algorithmModel P S).pairs) S.gradient ≠ 0 →
      ell * ‖modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
        (storedModel (algorithmModel P S).pairs) S.gradient‖ ^ 2 ≤ algorithmComputedCurvature P S ∧
      algorithmComputedCurvature P S ≤ trialUpper *
        ‖modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
          (storedModel (algorithmModel P S).pairs) S.gradient‖ ^ 2) :
    GradientRelated (dimensionDescentConstant n mu sigma upper trialUpper)
      (dimensionNormConstant n mu sigma upper ell) S.gradient (algorithmModel P S).direction := by
  let M := algorithmModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let c := fun i => ‖s i‖⁻¹
  have hc := krylov.Convergence.unitWindow_diagonal_unit s hs
  have hlen : M.pairs.length ≤ n := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hep : epsilon ≤ localStepRadius M.pairs.length mu sigma upper :=
    heps.trans (prefixMinimum_le _ n M.pairs.length hlen)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he hep).2.1
  have hdom := local_raw_window_domains H hH s y hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  have hdir : modelDirection (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y)
      (latest (crossGram (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y))) S.gradient =
        modelDirection s y (storedModel M.pairs) S.gradient := by
    rw [show latest (crossGram (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y)) =
      rescaleModel (latest (crossGram s y)) c from krylov.Convergence.ss1Model_rescale s y c]
    exact modelDirection_rescale s y _ c hc _
  have hbound := dimension_model_step_gradientRelated n hlen H hH
    (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y)
    (krylov.Convergence.unitWindow_norm s hs) mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he heps hpositive hHnorm hgain
    (unitWindow_reference_error H s y hs epsilon hy) S.gradient (algorithmComputedCurvature P S)
    (by simpa only [hdir] using htrial)
  change GradientRelated _ _ S.gradient
    (localModelStep (rescaleWindow s c) (rescaleWindow y c) S.gradient (algorithmComputedCurvature P S)) at hbound
  rw [localModelStep_rescale s y c hc] at hbound
  rw [algorithmModel_direction_eq_local P hoff S hp hdom.2.2.1]
  exact hbound

end
end krylov.XR
