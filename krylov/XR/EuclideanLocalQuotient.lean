import krylov.XR.EuclideanLocalSelected
import krylov.XR.LocalSelectedQuotient

/-!
Article: main_krylov, cor:xrF, Euclidean model actual Armijo quotient.
Use: derive the true scalar unit-trial quotient from the unchanged
primitive local theorem with the actual selected Euclidean matrix.
Source: true weighted Taylor energy and exact pair normalization.
-/
namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local instance euclideanQuotientDecidable (P : Prop) : Decidable P:=Classical.propDecidable P

/-- Genuine primitive data give the actual measured quotient estimate for
the literal selected-model direction, in unnormalized physical coordinates. -/
theorem euclideanAlgorithmModel_selected_quotient (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hp : (euclideanAlgorithmModel P S).pairs.length ≠ 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Hstar : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hHstar : Hstar.toLinearMap.IsSymmetric)
    (mu sigma upper ell trialUpper epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (he : 0 ≤ epsilon)
    (heps : epsilon ≤ dimensionStepRadius n mu sigma upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (Hstar v)) (hHnorm : ‖Hstar‖ ≤ upper)
    (hs : ∀ i, storedSteps (euclideanAlgorithmModel P S).pairs i ≠ 0)
    (hgain : ∀ w : Fin (euclideanAlgorithmModel P S).pairs.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps (euclideanAlgorithmModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (euclideanAlgorithmModel P S).pairs i - Hstar (storedSteps (euclideanAlgorithmModel P S).pairs i)‖ ≤
      epsilon * ‖storedSteps (euclideanAlgorithmModel P S).pairs i‖)
    (hmodel : ‖rescaleModel (selectedEuclideanModel P S.point (euclideanAlgorithmModel P S).pairs)
      (fun i => ‖storedSteps (euclideanAlgorithmModel P S).pairs i‖⁻¹) -
      localReferenceGram Hstar (krylov.Convergence.unitWindow (storedSteps (euclideanAlgorithmModel P S).pairs))‖ ≤
        ((euclideanAlgorithmModel P S).pairs.length : ℝ) * epsilon)
    (hg : S.gradient ≠ 0) (hcache : G S.point = S.gradient)
    (htrial : euclideanSelectedDirection P S ≠ 0 →
      ell * ‖euclideanSelectedDirection P S‖ ^ 2 ≤ euclideanComputedCurvature P S ∧
        euclideanComputedCurvature P S ≤ trialUpper * ‖euclideanSelectedDirection P S‖ ^ 2)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f
      (innerSL ℝ (G (S.point + t • (euclideanAlgorithmModel P S).direction))) (S.point + t • (euclideanAlgorithmModel P S).direction))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G
      (H (S.point + t • (euclideanAlgorithmModel P S).direction)) (S.point + t • (euclideanAlgorithmModel P S).direction))
    (hH : ContinuousOn (fun t : ℝ => H (S.point + t • (euclideanAlgorithmModel P S).direction)) (Icc 0 1))
    (herror : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (S.point + t • (euclideanAlgorithmModel P S).direction) - Hstar‖ ≤ epsilon) :
    let d := euclideanSelectedDirection P S
    trialQuotient f S.point S.gradient (euclideanAlgorithmModel P S).direction 1 ≤
      (if d = 0 then 1 else max 1 (inner ℝ (Hstar d) d / euclideanComputedCurvature P S)) +
        dimensionQuotientConstant n mu sigma ell * epsilon := by
  let M := euclideanAlgorithmModel P S
  let s := storedSteps M.pairs
  let y := storedImages M.pairs
  let T := selectedEuclideanModel P S.point M.pairs
  let sn := krylov.Convergence.unitWindow s
  let yn := krylov.Convergence.unitWindowImages s y
  let c := fun i => ‖s i‖⁻¹
  have hc := krylov.Convergence.unitWindow_diagonal_unit s hs
  have hlen : M.pairs.length ≤ n := (euclideanAlgorithmModel_length_le P S).trans (min_le_right _ _)
  have hep := heps.trans (prefixMinimum_le _ n M.pairs.length hlen)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he hep).2.1
  have hdom := local_raw_window_domains Hstar hHstar s y hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  have hdir : modelDirection sn yn (rescaleModel T c) S.gradient = euclideanSelectedDirection P S :=
    modelDirection_rescale s y T c hc S.gradient
  have hu : localModelStepWith sn yn (rescaleModel T c) S.gradient (euclideanComputedCurvature P S) = M.direction := by
    change localModelStepWith (rescaleWindow s c) (rescaleWindow y c) (rescaleModel T c) S.gradient _ = M.direction
    rw [localModelStepWith_rescale s y T c hc]
    exact (euclideanAlgorithmModel_direction_eq_selected_local P S hp hdom.2.2.1).symm
  have hq := primitive_local_model_quotient_with f G H Hstar hHstar sn yn (rescaleModel T c)
    (krylov.Convergence.unitWindow_norm s hs) mu sigma upper ell trialUpper epsilon
    hmu hsigma hupper hell htrialUpper he hep hpositive hHnorm hgain
    (unitWindow_reference_error Hstar s y hs epsilon hy) hmodel S.gradient S.point hg hcache (euclideanComputedCurvature P S)
    (by rw [hdir]; exact htrial)
    (by simpa only [hu] using hF) (by simpa only [hu] using hG)
    (by simpa only [hu] using hH) (by simpa only [hu] using herror)
  dsimp only at hq ⊢
  rw [hu, hdir] at hq
  have hm := mul_le_mul_of_nonneg_right
    (le_prefixMaximum (fun p => localQuotientConstant p mu sigma ell) n M.pairs.length hlen) he
  by_cases hd : euclideanSelectedDirection P S = 0
  · simp only [ite_eq_left hd] at hq ⊢
    exact hq.trans (add_le_add le_rfl hm)
  · simp only [ite_eq_right hd] at hq ⊢
    exact hq.trans (add_le_add le_rfl hm)


end
end krylov.XR
