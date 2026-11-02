import krylov.XR.EuclideanPracticalMemory
import krylov.XR.LocalSelectedQuotient

/-!
# Primitive local estimates for the practical model

Article Theorem 7.3 and Corollary 7.4. The true observed window and selected
F model are unchanged; only the positive missing-direction scalar differs.
All bounds below reuse the policy-independent local model estimates.
-/
namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual physical missing curvature supplied by the recent secant. -/
def euclideanPracticalComputedCurvature (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) : ℝ :=
  freshCurvature (fallbackCurvature S.bounds S.initialStep) S.pairs *
    ‖modelDirection (storedSteps (euclideanPracticalModel P S).pairs)
      (storedImages (euclideanPracticalModel P S).pairs)
      (selectedEuclideanModel P S.point (euclideanPracticalModel P S).pairs) S.gradient‖ ^ 2

/-- The actual new direction uses exactly the model selected by its real
value and Hermitian gates. -/
def euclideanPracticalSelectedDirection (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) :=
  modelDirection (storedSteps (euclideanPracticalModel P S).pairs) (storedImages (euclideanPracticalModel P S).pairs)
    (selectedEuclideanModel P S.point (euclideanPracticalModel P S).pairs) S.gradient

/-- Full actual physical rank forces the selected-model new direction
to vanish, independently of which value diagonal was selected. -/
theorem euclideanPracticalModel_selected_partial (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n)))
    (hinv : IsUnit (crossGram (storedImages (euclideanPracticalModel P S).pairs)
      (storedSteps (euclideanPracticalModel P S).pairs)).det)
    (hd : euclideanPracticalSelectedDirection P S ≠ 0) : (euclideanPracticalModel P S).pairs.length < n := by
  have hlen := (euclideanPracticalModel_length_le P S).trans (min_le_right _ _)
  have hnotfull : (euclideanPracticalModel P S).pairs.length ≠ n := by
    intro he
    have hspan := (euclideanPracticalModel_independent P S).span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_fin, finrank_euclideanSpace_fin]
      exact he)
    exact hd (modelDirection_zero_of_full_span _ _ _ hinv hspan _)
  omega

/-- The literal selected-model branch is the general local model step,
including the source full-window branch with its derived zero direction. -/
theorem euclideanPracticalModel_direction_eq_selected_local (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (euclideanPracticalModel P S).pairs.length ≠ 0)
    (hinv : IsUnit (crossGram (storedImages (euclideanPracticalModel P S).pairs)
      (storedSteps (euclideanPracticalModel P S).pairs)).det) :
    (euclideanPracticalModel P S).direction =
      localModelStepWith (storedSteps (euclideanPracticalModel P S).pairs) (storedImages (euclideanPracticalModel P S).pairs)
        (selectedEuclideanModel P S.point (euclideanPracticalModel P S).pairs) S.gradient (euclideanPracticalComputedCurvature P S) := by
  classical
  let M := euclideanPracticalModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := selectedEuclideanModel P S.point M.pairs
  let d := modelDirection s y T S.gradient
  by_cases hd : d = 0
  · have heq : M.direction = modelVirtualCorrection s T S.gradient := by
      change (if M.pairs.length = 0 then
        -(freshCurvature (fallbackCurvature S.bounds S.initialStep) S.pairs)⁻¹ • S.gradient
        else if M.pairs.length = n then modelVirtualCorrection s T S.gradient
        else modelTrialStep s y T S.gradient (euclideanPracticalComputedCurvature P S)) = _
      rw [ite_eq_right hp]
      split
      · rfl
      · exact modelTrialStep_zero_direction s y T S.gradient _ hd
    rw [heq]
    exact (ite_eq_left hd).symm
  · have hpartial := euclideanPracticalModel_selected_partial P S hinv hd
    change M.pairs.length < n at hpartial
    have heq : M.direction = modelTrialStep s y T S.gradient (euclideanPracticalComputedCurvature P S) := by
      change (if M.pairs.length = 0 then
        -(freshCurvature (fallbackCurvature S.bounds S.initialStep) S.pairs)⁻¹ • S.gradient
        else if M.pairs.length = n then modelVirtualCorrection s T S.gradient
        else modelTrialStep s y T S.gradient (euclideanPracticalComputedCurvature P S)) = _
      rw [ite_eq_right hp, ite_eq_right (by omega : M.pairs.length ≠ n)]
    rw [heq]
    exact (ite_eq_right hd).symm

/-- Source-only constants control the genuine selected raw model step in
physical unnormalized coordinates, for either setting of F. -/
theorem euclideanPracticalModel_selected_gradientRelated (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (euclideanPracticalModel P S).pairs.length ≠ 0)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : H.toLinearMap.IsSymmetric)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v)) (hHnorm : ‖H‖ ≤ upper)
    (hs : ∀ i, storedSteps (euclideanPracticalModel P S).pairs i ≠ 0)
    (hgain : ∀ w : Fin (euclideanPracticalModel P S).pairs.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps (euclideanPracticalModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (euclideanPracticalModel P S).pairs i - H (storedSteps (euclideanPracticalModel P S).pairs i)‖ ≤
      epsilon * ‖storedSteps (euclideanPracticalModel P S).pairs i‖)
    (hmodel : ‖rescaleModel (selectedEuclideanModel P S.point (euclideanPracticalModel P S).pairs)
      (fun i => ‖storedSteps (euclideanPracticalModel P S).pairs i‖⁻¹) -
      localReferenceGram H (krylov.Convergence.unitWindow (storedSteps (euclideanPracticalModel P S).pairs))‖ ≤
        ((euclideanPracticalModel P S).pairs.length : ℝ) * epsilon)
    (htrial : euclideanPracticalSelectedDirection P S ≠ 0 →
      ell * ‖euclideanPracticalSelectedDirection P S‖ ^ 2 ≤ euclideanPracticalComputedCurvature P S ∧
        euclideanPracticalComputedCurvature P S ≤ trialUpper * ‖euclideanPracticalSelectedDirection P S‖ ^ 2) :
    GradientRelated (dimensionDescentConstant n mu sigma upper trialUpper)
      (dimensionNormConstant n mu sigma upper ell) S.gradient (euclideanPracticalModel P S).direction := by
  let M := euclideanPracticalModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := selectedEuclideanModel P S.point M.pairs
  let c := fun i => ‖s i‖⁻¹
  have hc := krylov.Convergence.unitWindow_diagonal_unit s hs
  have hlen : M.pairs.length ≤ n := (euclideanPracticalModel_length_le P S).trans (min_le_right _ _)
  have hep := heps.trans (prefixMinimum_le _ n M.pairs.length hlen)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he hep).2.1
  have hdom := local_raw_window_domains H hH s y hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  have hdir : modelDirection (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y)
      (rescaleModel T c) S.gradient = euclideanPracticalSelectedDirection P S :=
    modelDirection_rescale s y T c hc S.gradient
  have hbound := local_general_model_gradientRelated H hH
    (krylov.Convergence.unitWindow s) (krylov.Convergence.unitWindowImages s y) (rescaleModel T c)
    (krylov.Convergence.unitWindow_norm s hs) mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he hep hpositive hHnorm hgain
    (unitWindow_reference_error H s y hs epsilon hy) hmodel S.gradient (euclideanPracticalComputedCurvature P S)
    (by rw [hdir]; exact htrial)
  change GradientRelated _ _ S.gradient
    (localModelStepWith (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) S.gradient _) at hbound
  rw [localModelStepWith_rescale s y T c hc] at hbound
  rw [euclideanPracticalModel_direction_eq_selected_local P S hp hdom.2.2.1]
  constructor
  · have hm := mul_le_mul_of_nonneg_right
      (prefixMinimum_le (fun p => localDescentConstant p mu sigma upper trialUpper) n M.pairs.length hlen)
      (sq_nonneg ‖S.gradient‖)
    exact hbound.1.trans (by dsimp only [dimensionDescentConstant]; linarith)
  · exact hbound.2.trans (mul_le_mul_of_nonneg_right
      (le_prefixMaximum (fun p => localNormConstant p mu sigma upper ell) n M.pairs.length hlen) (norm_nonneg _))

/-- Genuine primitive data give the actual measured quotient estimate for
the literal selected-model direction, in unnormalized physical coordinates. -/
theorem euclideanPracticalModel_selected_quotient (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (euclideanPracticalModel P S).pairs.length ≠ 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Hstar : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Hstar v)) (hHnorm : ‖Hstar‖ ≤ upper)
    (hs : ∀ i, storedSteps (euclideanPracticalModel P S).pairs i ≠ 0)
    (hgain : ∀ w : Fin (euclideanPracticalModel P S).pairs.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps (euclideanPracticalModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (euclideanPracticalModel P S).pairs i - Hstar (storedSteps (euclideanPracticalModel P S).pairs i)‖ ≤
      epsilon * ‖storedSteps (euclideanPracticalModel P S).pairs i‖)
    (hmodel : ‖rescaleModel (selectedEuclideanModel P S.point (euclideanPracticalModel P S).pairs)
      (fun i => ‖storedSteps (euclideanPracticalModel P S).pairs i‖⁻¹) -
      localReferenceGram Hstar (krylov.Convergence.unitWindow (storedSteps (euclideanPracticalModel P S).pairs))‖ ≤
        ((euclideanPracticalModel P S).pairs.length : ℝ) * epsilon)
    (hg : S.gradient ≠ 0) (hcache : G S.point = S.gradient)
    (htrial : euclideanPracticalSelectedDirection P S ≠ 0 →
      ell * ‖euclideanPracticalSelectedDirection P S‖ ^ 2 ≤ euclideanPracticalComputedCurvature P S ∧
        euclideanPracticalComputedCurvature P S ≤ trialUpper * ‖euclideanPracticalSelectedDirection P S‖ ^ 2)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f
      (innerSL ℝ (G (S.point + t • (euclideanPracticalModel P S).direction))) (S.point + t • (euclideanPracticalModel P S).direction))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G
      (H (S.point + t • (euclideanPracticalModel P S).direction)) (S.point + t • (euclideanPracticalModel P S).direction))
    (hH : ContinuousOn (fun t : ℝ => H (S.point + t • (euclideanPracticalModel P S).direction)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (S.point + t • (euclideanPracticalModel P S).direction) - Hstar‖ ≤ epsilon) :
    let d := euclideanPracticalSelectedDirection P S
    trialQuotient f S.point S.gradient (euclideanPracticalModel P S).direction 1 ≤
      (if d = 0 then 1 else max 1 (inner ℝ (Hstar d) d / euclideanPracticalComputedCurvature P S)) +
        dimensionQuotientConstant n mu sigma ell * epsilon := by
  let M := euclideanPracticalModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := selectedEuclideanModel P S.point M.pairs
  let sn := krylov.Convergence.unitWindow s
  let yn := krylov.Convergence.unitWindowImages s y
  let c := fun i => ‖s i‖⁻¹
  have hc := krylov.Convergence.unitWindow_diagonal_unit s hs
  have hlen : M.pairs.length ≤ n := (euclideanPracticalModel_length_le P S).trans (min_le_right _ _)
  have hep := heps.trans (prefixMinimum_le _ n M.pairs.length hlen)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he hep).2.1
  have hdom := local_raw_window_domains Hstar hHstar s y hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  have hdir : modelDirection sn yn (rescaleModel T c) S.gradient = euclideanPracticalSelectedDirection P S :=
    modelDirection_rescale s y T c hc S.gradient
  have hu : localModelStepWith sn yn (rescaleModel T c) S.gradient (euclideanPracticalComputedCurvature P S) = M.direction := by
    change localModelStepWith (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) S.gradient _ = M.direction
    rw [localModelStepWith_rescale s y T c hc]
    exact (euclideanPracticalModel_direction_eq_selected_local P S hp hdom.2.2.1).symm
  have hq := primitive_local_model_quotient_with f G H Hstar hHstar sn yn (rescaleModel T c)
    (krylov.Convergence.unitWindow_norm s hs) mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he hep hpositive hHnorm hgain
    (unitWindow_reference_error Hstar s y hs epsilon hy) hmodel S.gradient S.point hg hcache (euclideanPracticalComputedCurvature P S)
    (by rw [hdir]; exact htrial)
    (by simpa only [hu] using hF) (by simpa only [hu] using hG)
    (by simpa only [hu] using hH) (by simpa only [hu] using herror)
  dsimp only at hq ⊢
  rw [hu, hdir] at hq
  have hm := mul_le_mul_of_nonneg_right
    (le_prefixMaximum (fun p => localQuotientConstant p mu sigma ell) n M.pairs.length hlen) he
  by_cases hd : euclideanPracticalSelectedDirection P S = 0
  · simp only [ite_eq_left hd] at hq ⊢
    exact hq.trans (add_le_add le_rfl hm)
  · simp only [ite_eq_right hd] at hq ⊢
    exact hq.trans (add_le_add le_rfl hm)

end
end krylov.XR
