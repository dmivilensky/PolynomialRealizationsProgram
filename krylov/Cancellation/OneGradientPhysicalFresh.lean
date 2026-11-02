import krylov.Cancellation.OneGradientFreshObstruction
import krylov.Cancellation.PhysicalFreshDefect
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), full native physical fresh obstruction.
Use: prove the printed finite-variation lower bound on the actual selected
window of every original one-gradient method, with actual physical matrices.
Source: genuine prefix indistinguishability and the proved symmetric
Householder witness in the exact inverse-energy-Gram norm.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every original one-gradient executor has indistinguishable opposite real
physical fresh scenarios, one of whose genuine next observations leaves the
full printed window residual lower bound.
Use: both the retained window and chosen step come from the actual incoming
execution; no response, common-history field or regularity is assumed.
Article: main_krylov, apH:dcs2(a), original finite-variation lower bound.
Proof: use the actual nonempty independent retained window in the proved
physical reflection construction. The native fresh-prefix theorem proves
that both real executions have the same complete incoming histories and
same chosen step. Their actual new gradients are the required opposite
physical updates, so the sharp physical two-scenario bound applies. -/
theorem one_gradient_physical_fresh_obstruction
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin n)))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (memory : ℕ → ℕ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hp : 0<(selectedWindow memory (oneGradientRun m A g k)).length)
    (hs : LinearIndependent ℝ (windowSteps (selectedWindow memory (oneGradientRun m A g k))))
    (omega : ℝ) (homega : 0≤omega) :
    let W := selectedWindow memory (oneGradientRun m A g k)
    let step := oneGradientStep m A g k
    ∃ F : Matrix (Fin n) (Fin n) ℝ,F.IsSymm ∧ ‖relativeOperator base F‖≤omega ∧
      (∀ j≤k,oneGradientRun m (freshOperatorPath A k (cgOperator F)) g j=
        oneGradientRun m (freshOperatorPath A k (-cgOperator F)) g j) ∧
      windowMetricResidual base (windowSteps W) (cgOperator F step)=omega*‖cgOperator (metricRoot base) step‖ ∧
      omega*‖cgOperator (metricRoot base) step‖≤
        max (windowMetricResidual base (windowSteps W)
          (oneGradientGradient m (freshOperatorPath A k (cgOperator F)) g (k+1)))
          (windowMetricResidual base (windowSteps W)
            (oneGradientGradient m (freshOperatorPath A k (-cgOperator F)) g (k+1))) := by
  let W := selectedWindow memory (oneGradientRun m A g k)
  let step := oneGradientStep m A g k
  obtain ⟨F,hFs,hF,himage,hlower⟩ := physical_fresh_projection_witness base hb (windowSteps W) hs hp
    step (oneGradientGradient m A g (k+1)) omega homega
  refine ⟨F,hFs,hF,fun j hj => (one_gradient_fresh_prefix m A g k (cgOperator F) j hj).trans
    (one_gradient_fresh_prefix m A g k (-cgOperator F) j hj).symm,himage,?_⟩
  rw [one_gradient_fresh_gradient,one_gradient_fresh_gradient]
  simpa only [_root_.neg_apply,sub_eq_add_neg] using hlower

end
end krylov.Cancellation
