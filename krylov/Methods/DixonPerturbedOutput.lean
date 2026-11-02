import krylov.Methods.DirectBFGSInverse
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), true nonquadratic Dixon inverse output.
Use: retain the literal accumulated two-loop BFGS output in the full
second-order comparison with latest information on the same actual pairs.
Source: exact native direct/inverse BFGS dictionary and the full original
native perturbation theorem; all true positive pair domains are derived.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant
open Matrix Filter Topology Asymptotics
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {α : Type*} {n : ℕ} {l : Filter α} {t : α → ℝ}

/-- On the original primitive varying-segment source class, the literal
full-memory two-loop BFGS output and the true latest-information correction
on its own actual pairs differ by O(t² norm g), for every actual final
gradient. No surrogate output, model comparison or native rate is assumed.
Use: closes the actual Dixon quasi-Newton final-step source comparison.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the real pair limits give all actual positive observed curvatures.
The original identity initialization and true zero direct parameter make
the native direct model the genuine BFGS direct recursion. Its exact
inverse is the actual two-loop implementation, so the proved native
physical inverse estimate applies to the literal output. -/
theorem dixon_bfgs_perturbed_final_step
    (D : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t n)
    (hId : D.initial=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (hphi : ∀ z i,i< n → D.parameter z i=0)
    (hli : LinearIndependent ℝ (fun i : Fin n => D.referenceStep i.val))
    (g : α → EuclideanSpace ℝ (Fin n)) :
    (fun z => -inverseBFGSApply 1 (directBroydenRecords (directBroydenPerturbedPairs D z) n) (g z)+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (directBroydenPhysicalSteps D z*
        (latest (directBroydenPhysicalObserved D z))⁻¹*(directBroydenPhysicalSteps D z)ᵀ) (g z))
      =O[l] (fun z => t z^2*‖g z‖) := by
  have h := directBroyden_physical_final_step_second_order D hli g
  have hp : ∀ᶠ z in l,∀ i : Fin n,0 < inner ℝ (D.step z i.val) (D.image z i.val) :=
    eventually_all.mpr (fun i => (directBroydenPerturbation_pair_bounds D i.val i.isLt).2.2.2.2)
  apply h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hp] with z hz
  have hpairs : ∀ q∈directBroydenRecords (directBroydenPerturbedPairs D z) n,
      0 < inner ℝ q.1 q.2 := by
    rw [directBroydenRecords_ofFn]
    exact List.forall_mem_ofFn_iff.mpr (fun i => hz ⟨n-1-i.val,by omega⟩)
  have hmodel : directBroydenPerturbedModel D z n=
      directBroydenOperatorModel (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (fun _ => 0)
        (directBroydenRecords (directBroydenPerturbedPairs D z) n) := by
    unfold directBroydenPerturbedModel directBroydenNative
    rw [hId]
    apply directBroydenOperatorModel_schedule_congr
    intro i hi
    exact hphi z i (by simpa only [directBroydenRecords_length] using hi)
  have he := directBFGS_physical_inverse_action _ hpairs (g z)
  change -(Matrix.toEuclideanCLM (𝕜 := ℝ)
    (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (directBroydenPerturbedModel D z n))⁻¹) (g z))+_= _
  rw [hmodel,he]

end
end krylov.Methods
