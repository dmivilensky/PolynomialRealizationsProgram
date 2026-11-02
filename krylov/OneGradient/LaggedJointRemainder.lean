import krylov.OneGradient.LaggedCancellation
import krylov.OneGradient.XRFCStepCompact
import krylov.OneGradient.XRFCDirectionCompact
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb(a), joint quadratic lagged output bound.
Use: the cancellation gives a uniform norm-squared estimate in a full finite
perturbation chart, not merely on a separately chosen scalar path.
Source: actual primitive lagged smoothness and the existing compact joint
XRFC expansions, with coefficientwise cancellation of their true responses.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Stability krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The original lagged method has one genuine quadratic norm remainder
throughout a full finite perturbation neighborhood of a constant-length
reference in either actual basis, with no assumed trial regularity.
Use: canonical finite increment charts give the source O(norm(E)^2) assertion.
Article: main_krylov, prop:hb(a).
Proof: the actual lagged observed-coordinate rules are C-two at the true
reference. Apply the proved native compact joint expansion to its singleton;
every genuine measured amplitude vanishes, so its entire linear term is zero. -/
theorem lagged_constant_output_joint (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 2≤n)
    (alpha : ℝ) (halpha : ∀ i<n,CG.length (cgOperator base) g i=alpha)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 2 (fun x => A x k) 0)
    (hsym : ∀ x k,(A x k).IsSymm) (hA0 : ∀ k,A 0 k=base) :
    let method := xrfcBasisMethod directions (laggedTrial directions tau0)
    let op := fun x k => cgOperator (A x k)
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ h : X,‖h‖≤delta →
      ‖cgOperator (metricRoot base)⁻¹
        (method.outputGradient (op h n) (oneGradientRun method (op h) g n))‖≤
          C*‖h‖^2*‖cgOperator (metricRoot base)⁻¹ g‖ := by
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by omega)
  have hT := fun (k : ℕ) (hk : k<n) => lagged_trial_reference_contDiff (r := 2) directions htau0
    (cgOperator base) hp.1 hp.2 g n hpre k hk.le
  have hAref (x : X) (hx : x∈({0} : Set X)) (k : ℕ) : A x k=base := by
    rw [Set.mem_singleton_iff.mp hx]
    exact hA0 k
  cases directions with
  | false =>
    obtain ⟨delta,C,hd,hC,hrem⟩ := xrfc_step_compact_expansion (laggedTrial false tau0)
      (fun _ : X => base) (fun _ => g) A {0} isCompact_singleton (by omega)
      (fun _ _ => contDiffAt_const) (fun _ _ => Eventually.of_forall (fun _ => hb))
      (fun x hx k => by rw [Set.mem_singleton_iff.mp hx];exact hA k) (fun _ _ => contDiffAt_const)
      hsym hAref (fun _ _ => hc) (fun _ _ _ _ => (lagged_trial_positive false htau0 _).ne')
      (fun _ _ => hT)
    refine ⟨delta,C,hd,hC,?_⟩
    intro h hh
    have hbnd := hrem 0 (Set.mem_singleton 0) h hh (fun _ => rfl) (fun _ => rfl)
    dsimp only at hbnd
    rw [zero_add,(lagged_constant_responses false htau0 base hb g hc hn alpha halpha _).2,sub_zero] at hbnd
    exact hbnd
  | true =>
    obtain ⟨delta,C,hd,hC,hrem⟩ := xrfc_direction_compact_expansion (laggedTrial true tau0)
      (fun _ : X => base) (fun _ => g) A {0} isCompact_singleton (by omega)
      (fun _ _ => contDiffAt_const) (fun _ _ => Eventually.of_forall (fun _ => hb))
      (fun x hx k => by rw [Set.mem_singleton_iff.mp hx];exact hA k) (fun _ _ => contDiffAt_const)
      hAref (fun _ _ => hc) (fun _ _ _ _ => (lagged_trial_positive true htau0 _).ne')
      (fun _ _ => hT)
    refine ⟨delta,C,hd,hC,?_⟩
    intro h hh
    have hbnd := hrem 0 (Set.mem_singleton 0) h hh (fun _ => rfl) (fun _ => rfl)
    dsimp only at hbnd
    rw [zero_add,(lagged_constant_responses true htau0 base hb g hc hn alpha halpha _).1,sub_zero] at hbnd
    exact hbnd

end
end krylov.OneGradient
