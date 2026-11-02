import krylov.XR.LocalGeneralQuotient
import krylov.XR.LocalModelStep

/-!
Article: main_krylov, apG:local and cor:xrF, literal selected-model bounds.
Use: connect the executor's actually selected T to the general primitive
local theorems. All pair normalization is exact, and the full-window
zero direction is derived from true physical rank and the observed solve.
Source: the literal ModelStep decomposition and proved coefficient geometry.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual new direction uses exactly the model selected by its real
value and Hermitian gates. -/
def algorithmSelectedDirection (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) :=
  modelDirection (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
    (selectedModel P (algorithmModel P S).pairs) S.gradient

/-- Full actual physical rank forces the selected-model new direction
to vanish, independently of which value diagonal was selected. -/
theorem algorithmModel_selected_partial (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n)))
    (hinv : IsUnit (crossGram (storedImages (algorithmModel P S).pairs)
      (storedSteps (algorithmModel P S).pairs)).det)
    (hd : algorithmSelectedDirection P S ≠ 0) : (algorithmModel P S).pairs.length < n := by
  have hlen := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hnotfull : (algorithmModel P S).pairs.length ≠ n := by
    intro he
    have hspan := (algorithmModel_independent P S).span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
      exact he)
    exact hd (modelDirection_zero_of_full_span _ _ _ hinv hspan _)
  omega

/-- The literal selected-model branch is the general local model step,
including the source full-window branch with its derived zero direction. -/
theorem algorithmModel_direction_eq_selected_local (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (algorithmModel P S).pairs.length ≠ 0)
    (hinv : IsUnit (crossGram (storedImages (algorithmModel P S).pairs)
      (storedSteps (algorithmModel P S).pairs)).det) :
    (algorithmModel P S).direction =
      localModelStepWith (storedSteps (algorithmModel P S).pairs) (storedImages (algorithmModel P S).pairs)
        (selectedModel P (algorithmModel P S).pairs) S.gradient (algorithmComputedCurvature P S) := by
  classical
  let M := algorithmModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := selectedModel P M.pairs
  let d := modelDirection s y T S.gradient
  have hdecomp := algorithmModel_direction_decomposition P S hp
  change M.direction = modelVirtualCorrection s T S.gradient + algorithmTrialParameter P S • d at hdecomp
  by_cases hd : d = 0
  · rw [hd, smul_zero, add_zero] at hdecomp
    change M.direction = localModelStepWith s y T S.gradient _
    rw [hdecomp]
    exact (ite_eq_left hd).symm
  · have hpartial := algorithmModel_selected_partial P S hinv hd
    change M.pairs.length < n at hpartial
    have hparameter : algorithmTrialParameter P S = modelTrialLength s y T S.gradient (algorithmComputedCurvature P S) := by
      change (if M.pairs.length = 0 then
        (match M.bounds with | none => S.initialStep | some b => 2 / (b.1 + b.2))
        else if M.pairs.length = n ∨ d = 0 then 0
        else modelTrialLength s y T S.gradient (algorithmComputedCurvature P S)) = _
      rw [ite_eq_right hp, ite_eq_right (not_or.mpr ⟨by omega, hd⟩)]
    change M.direction = localModelStepWith s y T S.gradient _
    rw [hdecomp, hparameter]
    exact (ite_eq_right hd).symm

/-- Source-only constants control the genuine selected raw model step in
physical unnormalized coordinates, for either setting of F. -/
theorem algorithmModel_selected_gradientRelated (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (algorithmModel P S).pairs.length ≠ 0)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : H.toLinearMap.IsSymmetric)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v)) (hHnorm : ‖H‖ ≤ upper)
    (hs : ∀ i, storedSteps (algorithmModel P S).pairs i ≠ 0)
    (hgain : ∀ w : Fin (algorithmModel P S).pairs.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps (algorithmModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (algorithmModel P S).pairs i - H (storedSteps (algorithmModel P S).pairs i)‖ ≤
      epsilon * ‖storedSteps (algorithmModel P S).pairs i‖)
    (hmodel : ‖rescaleModel (selectedModel P (algorithmModel P S).pairs)
      (fun i => ‖storedSteps (algorithmModel P S).pairs i‖⁻¹) -
      localReferenceGram H (krylov.Convergence.unitWindow (storedSteps (algorithmModel P S).pairs))‖ ≤
        ((algorithmModel P S).pairs.length : ℝ) * epsilon)
    (htrial : algorithmSelectedDirection P S ≠ 0 →
      ell * ‖algorithmSelectedDirection P S‖ ^ 2 ≤ algorithmComputedCurvature P S ∧
        algorithmComputedCurvature P S ≤ trialUpper * ‖algorithmSelectedDirection P S‖ ^ 2) :
    GradientRelated (dimensionDescentConstant n mu sigma upper trialUpper)
      (dimensionNormConstant n mu sigma upper ell) S.gradient (algorithmModel P S).direction := by
  let M := algorithmModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := selectedModel P M.pairs
  let c := fun i => ‖s i‖⁻¹
  have hc := krylov.Convergence.unitWindow_diagonal_unit s hs
  have hlen : M.pairs.length ≤ n := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hep := heps.trans (prefixMinimum_le _ n M.pairs.length hlen)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he hep).2.1
  have hdom := local_raw_window_domains H hH s y hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  have hdir : modelDirection (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y)
      (rescaleModel T c) S.gradient = algorithmSelectedDirection P S :=
    modelDirection_rescale s y T c hc S.gradient
  have hbound := local_general_model_gradientRelated H hH
    (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y) (rescaleModel T c)
    (krylov.Convergence.unitWindow_norm s hs) mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he hep hpositive hHnorm hgain
    (unitWindow_reference_error H s y hs epsilon hy) hmodel S.gradient (algorithmComputedCurvature P S)
    (by rw [hdir]; exact htrial)
  change GradientRelated _ _ S.gradient
    (localModelStepWith (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) S.gradient _) at hbound
  rw [localModelStepWith_rescale s y T c hc] at hbound
  rw [algorithmModel_direction_eq_selected_local P S hp hdom.2.2.1]
  constructor
  · have hm := mul_le_mul_of_nonneg_right
      (prefixMinimum_le (fun p => localDescentConstant p mu sigma upper trialUpper) n M.pairs.length hlen)
      (sq_nonneg ‖S.gradient‖)
    exact hbound.1.trans (by dsimp only [dimensionDescentConstant]; linarith)
  · exact hbound.2.trans (mul_le_mul_of_nonneg_right
      (le_prefixMaximum (fun p => localNormConstant p mu sigma upper ell) n M.pairs.length hlen) (norm_nonneg _))

end
end krylov.XR
