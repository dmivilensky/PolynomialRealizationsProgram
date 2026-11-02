import krylov.Correction.RFCSJoint
import krylov.Stability.CompactZeroQuadratic

/-!
Article: main_krylov, thm:RFCS, actual compact-reference source remainder.
Use: Prove one genuine quadratic RFC-S operator remainder tube uniformly
before every compact family of actual full active initial-gradient references.
Source: actual joint RFC-S prefix and leading-coefficient analyticity,
proved pointwise only-last-probe expansion and compact zero-jet Taylor theorem.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant krylov.Variation krylov.Envelope
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {k : ℕ}

/-- The genuine actual normalized RFC-S terminal output minus its original independent last-probe leading action on the true reference step.
Use: Supply genuine compact-reference constants for the original nonlinear restarted RFC-S consequence.
Article: main_krylov, thm:RFCS, compact-reference actual operator remainder.
-/
def rfcsJointRemainder (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1)) : EuclideanSpace ℝ (Fin (k+1)) :=
  rfcsJointOutput base z-rfcsJointLeading base z

/-- The actual RFC-S remainder is jointly analytic in its true initial-gradient and finite source parameters at every full active reference.
Use: Supply genuine compact-reference constants for the original nonlinear restarted RFC-S consequence.
Article: main_krylov, thm:RFCS, compact-reference actual operator remainder.
Proof: The genuine pointwise source expansion identifies the original leading action; actual joint analyticity and the compact zero-jet Taylor theorem make its quadratic remainder uniform.
-/
theorem rfcs_joint_remainder_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (rfcsJointRemainder base) (g,0) :=
  (rfcs_joint_output_analytic base hb g hN).sub (rfcs_joint_leading_analytic base hb g hN)

/-- The true jointly defined original RFC-S remainder has quadratic source order at every genuine full active reference.
Use: Supply genuine compact-reference constants for the original nonlinear restarted RFC-S consequence.
Article: main_krylov, thm:RFCS, compact-reference actual operator remainder.
Proof: The genuine pointwise source expansion identifies the original leading action; actual joint analyticity and the compact zero-jet Taylor theorem make its quadratic remainder uniform.
-/
theorem rfcs_joint_remainder_order (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    (fun Θ : symmetricScenarios (k+1) (k+1) => rfcsJointRemainder base (g,Θ)) =O[𝓝 0] (fun Θ => ‖Θ‖^2) := by
  -- Use the already proved actual only-last-probe expansion and identify its original true reference step exactly.
  have hr := full_rfcs_canonical_first_order base hb g hN hk
    (fun Θ : symmetricScenarios (k+1) (k+1) => matrixSequenceExtension k Θ.val.1)
    (fun Θ => matrixSequenceExtension (k+1) Θ.val.2)
    symmetricScenario_increment_analytic symmetricScenario_correction_analytic
    (fun i => matrixSequenceExtension_zero k i) (fun i => matrixSequenceExtension_zero (k+1) i)
  apply hr.congr_left
  intro Θ
  change cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)-
      ‖canonicalCGStep base g k‖ • cgOperator (matrixSequenceExtension (k+1) Θ.val.2 k) (canonicalCGUnitStep base g k)=
    cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)-
      cgOperator (matrixSequenceExtension (k+1) Θ.val.2 k) (rfcsReferenceStep base g)
  rw [rfcsReferenceStep_eq_cg base hb]
  have hstep : ‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k=canonicalCGStep base g k :=
    NormedSpace.norm_smul_normalize _
  rw [← map_smul,hstep]

/-- One actual quadratic operator remainder tube covers every original finite symmetric source and every initial gradient in a compact family of full active references.
Use: Supply genuine compact-reference constants for the original nonlinear restarted RFC-S consequence.
Article: main_krylov, thm:RFCS, compact-reference actual operator remainder.
Proof: The genuine pointwise source expansion identifies the original leading action; actual joint analyticity and the compact zero-jet Taylor theorem make its quadratic remainder uniform.
-/
theorem compact_rfcs_scenario_quadratic_tube (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K, ∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖≤δ →
      ‖cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)-
        cgOperator (matrixSequenceExtension (k+1) Θ.val.2 k) (canonicalCGStep base g k)‖≤C*‖Θ‖^2 := by
  -- The actual joint analytic locus supplies one compact tube, while pointwise quadratic vanishing removes every genuine first perturbation jet.
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_zero_quadratic (rfcsJointRemainder base) K hK
    (fun g hg => rfcs_joint_remainder_analytic base hb g (hN g hg))
    (fun g hg => rfcs_joint_remainder_order base hb g (hN g hg) hk)
  refine ⟨δ,C+1,hδ,by linarith,?_⟩
  intro g hg Θ hΘ
  have hh := hbound g hg Θ hΘ
  change ‖rfcsJointOutput base (g,Θ)-rfcsJointLeading base (g,Θ)‖≤_ at hh
  simp only [rfcsJointOutput,rfcsJointLeading,rfcsReferenceStep_eq_cg base hb] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : C≤C+1) (sq_nonneg ‖Θ‖))

end
end krylov.Correction
