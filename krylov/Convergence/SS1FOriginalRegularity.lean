import krylov.Convergence.SS1FRate
import krylov.Convergence.SecantThirdVariation

/-!
Article: main_krylov, thm:ss1F, original C3,1 source hypotheses.
Use: discharge every auxiliary Hessian Lipschitz and tensor-budget input
from the actual scalar third derivative on the bounded convex local domain.
Source: the real Riesz isometry and the proved sharp symmetric cubic norm
identity; the actual sequence and delayed recurrence are unchanged.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Original spectral C3,1 regularity alone supplies all derivative budgets
in the actual SS1-F improved recurrence and characteristic R-order. -/
theorem ss1FSequence_original_regular_rorder
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {R : ℝ} (hR : 0≤R) (hbounded : ∀ z∈S,‖z‖≤R) {L₃ : ℝ≥0} (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (split : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+1))) → Fin (n+1) → ℝ)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+n+1))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+n+1)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    (∃ K : ℝ,0<K ∧∀ᶠ k in atTop,
      ‖ss1FSequence f G split seed (k+1)‖≤K*‖ss1FSequence f G split seed k‖*
        (‖ss1FSequence f G split seed (k-n)‖+‖ss1FSequence f G split seed (k-(n+1))‖^2)) ∧
    HasROrder (fun k=>‖ss1FSequence f G split seed k‖) (oneGradientRoot (n+1)) := by
  have hH := hessian_lipschitz_of_scalar_third H T S hS h₀ hT L₃ hLip hR hbounded
  exact ss1FSequence_improved_rorder f G H T S hS h₀ hnbhd hH hH₀ hf hG hG₀ hT hLip
    (norm_nonneg (canonicalVariation (T 0)))
    (canonicalVariation_unit_diagonal_bound (T 0)) split seed hconv hCw hσ hw hind

end
end krylov.Convergence
