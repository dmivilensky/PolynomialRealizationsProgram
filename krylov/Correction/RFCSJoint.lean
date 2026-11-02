import krylov.Correction.RFCSSource
import krylov.Stability.WeightedCompactTaylor
import krylov.Methods.ReferenceProbedSteps

/-!
Article: main_krylov, thm:RFCS, genuine joint reference/source regularity.
Use: Prove actual RFC-S joint analyticity in the initial gradient and all
independent finite source operators, including every true prefix field and
the genuine only-last-probe linear coefficient on its full reference domain.
Source: primitive exact finite symmetric source coordinates, actual RFC-S
quadratic reference domains, existing analytic observed-prefix induction and
genuine global CG consistency of the real full-memory RFC executor.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant krylov.Variation krylov.Envelope
open scoped Matrix.Norms.L2Operator InnerProductSpace
set_option maxHeartbeats 600000
variable {k : ℕ}

/-- The genuine physical segment operator sequence on the joint initial-gradient and original finite symmetric source space.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
-/
def rfcsJointLine (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1)) :=
  canonicalFCPath base (matrixSequenceExtension k z.2.val.1) 1

/-- The genuine independently measured probe sequence on the joint original initial-gradient and finite source space.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
-/
def rfcsJointProbe (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1)) :=
  rfcsCanonicalProbe base (matrixSequenceExtension k z.2.val.1) (matrixSequenceExtension (k+1) z.2.val.2)

/-- The actual normalized terminal RFC-S gradient on the joint genuine reference/source parameter space.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
-/
def rfcsJointOutput (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1)) :=
  cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base z.1 z.2)

/-- Every genuine original line and independent probe operator is jointly analytic at every positive zero-source reference.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
Proof: Use primitive source analyticity and the genuine quadratic RFC-S execution with actual measured histories and globally CG-consistent reference steps.
-/
theorem rfcs_joint_operators_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    (∀ i, AnalyticAt ℝ (fun z => rfcsJointLine base z i) (g,0)) ∧
      (∀ i, AnalyticAt ℝ (fun z => rfcsJointProbe base z i) (g,0)) := by
  -- Keep the genuine initial gradient as an independent reference coordinate while every original finite operator coordinate stays in the unchanged source space.
  let E := fun z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1) => matrixSequenceExtension k z.2.val.1
  let P := fun z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1) => matrixSequenceExtension (k+1) z.2.val.2
  have hE (i : ℕ) : AnalyticAt ℝ (fun z => E z i) (g,0) := by
    exact (symmetricScenario_increment_analytic (n := k+1) (N := k+1) i).comp (f := Prod.snd) (x := (g,0)) analyticAt_snd
  have hP (i : ℕ) : AnalyticAt ℝ (fun z => P z i) (g,0) := by
    exact (symmetricScenario_correction_analytic (n := k+1) (N := k+1) i).comp (f := Prod.snd) (x := (g,0)) analyticAt_snd
  have hA (i : ℕ) : AnalyticAt ℝ (fun z => rfcsJointLine base z i) (g,0) :=
    canonicalFCPath_analyticAt (fun _ => base) E (g,0) analyticAt_const (Filter.Eventually.of_forall fun _ => hb) hE i
  refine ⟨hA,?_⟩
  intro i
  have hm : AnalyticAt ℝ (fun z => metricRoot base*P z i*metricRoot base) (g,0) :=
    (analyticAt_const.mul (hP i)).mul analyticAt_const
  exact (hA i).sub ((matrixOperator_contDiffAt _ _ hm.contDiffAt).analyticAt)

/-- The genuine original joint line and independent probe sequences both equal the true fixed quadratic operator at zero source.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
Proof: Use primitive source analyticity and the genuine quadratic RFC-S execution with actual measured histories and globally CG-consistent reference steps.
-/
theorem rfcs_joint_operators_zero (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    rfcsJointLine base (g,0)=(fun _ => cgOperator base) ∧
      rfcsJointProbe base (g,0)=(fun _ => cgOperator base) := by
  have hA : rfcsJointLine base (g,0)=(fun _ => cgOperator base) :=
    canonicalFCPath_at_zero base _ (fun i => matrixSequenceExtension_zero k i)
  refine ⟨hA,?_⟩
  funext i
  have hP : matrixSequenceExtension (k+1) (0 : symmetricScenarios (k+1) (k+1)).val.2 i=0 :=
    matrixSequenceExtension_zero (k+1) i
  change canonicalFCPath base (matrixSequenceExtension k (0 : symmetricScenarios (k+1) (k+1)).val.1) 1 i-
    cgOperator (metricRoot base*matrixSequenceExtension (k+1) (0 : symmetricScenarios (k+1) (k+1)).val.2 i*metricRoot base)=_
  rw [hP,Matrix.mul_zero,Matrix.zero_mul]
  simp only [cgOperator,map_zero,sub_zero]
  exact congrFun hA i

/-- Every actual RFC-S terminal gradient, direction, recorded total step and measured secant is jointly analytic through each active finite quadratic prefix, including the varying initial gradient.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
Proof: Use primitive source analyticity and the genuine quadratic RFC-S execution with actual measured histories and globally CG-consistent reference steps.
-/
theorem rfcs_joint_prefix_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (N : ℕ) (hN : N≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (fun z => rfcSGradient fullMemory (rfcsJointProbe base z)
      (rfcsJointLine base z) (rfcsJointLine base z) z.1 N) (g,0) ∧
    ∀ i<N,
      AnalyticAt ℝ (fun z => rfcSDirection fullMemory (rfcsJointProbe base z)
        (rfcsJointLine base z) (rfcsJointLine base z) z.1 i) (g,0) ∧
      AnalyticAt ℝ (fun z => rfcSStep fullMemory (rfcsJointProbe base z)
        (rfcsJointLine base z) (rfcsJointLine base z) z.1 i) (g,0) ∧
      AnalyticAt ℝ (fun z => rfcSSecant fullMemory (rfcsJointProbe base z)
        (rfcsJointLine base z) (rfcsJointLine base z) z.1 i) (g,0) := by
  have hop := rfcs_joint_operators_analytic base hb g
  have hz := rfcs_joint_operators_zero base g
  have hQ := cgOperator_positive base hb
  exact quadraticRFCS_prefix_analytic fullMemory (rfcsJointProbe base) (rfcsJointLine base) (rfcsJointLine base)
    Prod.fst (g,0) hop.2 hop.1 hop.1 analyticAt_fst (cgOperator base) hz.2 hz.1 hz.1 hQ.1 hQ.2
    (fun _ _ hj => hj) N (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hN))

/-- The actual normalized full RFC-S terminal output is jointly analytic in the initial gradient and all original source operators at every full active reference.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
Proof: Use primitive source analyticity and the genuine quadratic RFC-S execution with actual measured histories and globally CG-consistent reference steps.
-/
theorem rfcs_joint_output_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (rfcsJointOutput base) (g,0) := by
  change AnalyticAt ℝ (fun z => cgOperator (metricRoot base)⁻¹
    (rfcSGradient fullMemory (rfcsJointProbe base z) (rfcsJointLine base z) (rfcsJointLine base z) z.1 (k+1))) (g,0)
  exact ((cgOperator (metricRoot base)⁻¹).analyticAt _).comp (rfcs_joint_prefix_analytic base hb g (k+1) hN).1


/-- The genuine final reference RFC-S step transported to its actual canonical coordinates.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
-/
def rfcsReferenceStep (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  cgOperator (metricRoot base) (rfcSStep fullMemory (fun _ => cgOperator base)
    (fun _ => cgOperator base) (fun _ => cgOperator base) g k)

/-- The actual reference RFC-S step is exactly the original genuine canonical CG step for every initial gradient, including stopped tails.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
Proof: Use primitive source analyticity and the genuine quadratic RFC-S execution with actual measured histories and globally CG-consistent reference steps.
-/
theorem rfcsReferenceStep_eq_cg (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) : rfcsReferenceStep base g=canonicalCGStep base g k := by
  have hQ := cgOperator_positive base hb
  rw [rfcsReferenceStep,(rfcSFields_exact fullMemory (fun _ => cgOperator base) (fun _ => cgOperator base) g k).2.2.1]
  rw [quadratic_probedStep_eq_cg _ (rfcMethod_consistent fullMemory (fun _ h => h) 1) _ hQ.1 hQ.2]
  rfl

/-- The actual final canonical reference step is analytic in its genuine initial gradient near every full active reference.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
Proof: Use primitive source analyticity and the genuine quadratic RFC-S execution with actual measured histories and globally CG-consistent reference steps.
-/
theorem rfcsReferenceStep_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (rfcsReferenceStep base) g := by
  -- Restrict the genuine jointly analytic executed step to the true zero-source reference slice before applying the actual canonical root.
  have hs := ((rfcs_joint_prefix_analytic base hb g (k+1) hN).2 k (Nat.lt_succ_self k)).2.1
  have ht := hs.comp (f := fun v : EuclideanSpace ℝ (Fin (k+1)) => (v,0))
    (analyticAt_id.prod analyticAt_const)
  have hA : ∀ v : EuclideanSpace ℝ (Fin (k+1)), rfcsJointLine base (v,0)=(fun _ => cgOperator base) :=
    fun v => (rfcs_joint_operators_zero base v).1
  have hP : ∀ v : EuclideanSpace ℝ (Fin (k+1)), rfcsJointProbe base (v,0)=(fun _ => cgOperator base) :=
    fun v => (rfcs_joint_operators_zero base v).2
  dsimp only [Function.comp_def] at ht
  simp only [hA,hP] at ht
  change AnalyticAt ℝ (fun v => cgOperator (metricRoot base)
    (rfcSStep fullMemory (fun _ => cgOperator base) (fun _ => cgOperator base) (fun _ => cgOperator base) v k)) g
  exact ((cgOperator (metricRoot base)).analyticAt _).comp ht

/-- The actual original final independent probe mismatch acting on its genuine canonical reference step.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
-/
def rfcsJointLeading (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1)) :=
  cgOperator (matrixSequenceExtension (k+1) z.2.val.2 k) (rfcsReferenceStep base z.1)

/-- The genuine only-last-probe leading coefficient is jointly analytic in its actual reference and source parameters.
Use: Supply actual compact-reference source regularity for the original nonlinear RFC-S transfer.
Article: main_krylov, thm:RFCS, genuine joint initial-gradient and source dependence.
Proof: Use primitive source analyticity and the genuine quadratic RFC-S execution with actual measured histories and globally CG-consistent reference steps.
-/
theorem rfcs_joint_leading_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (rfcsJointLeading base) (g,0) := by
  -- The true final probe matrix is linear in source coordinates, while its actual canonical reference step is analytic in the separate initial-gradient coordinate.
  have hP : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1) =>
      matrixSequenceExtension (k+1) z.2.val.2 k) (g,0) := by
    simpa only [Function.comp_def] using
      (symmetricScenario_correction_analytic (n := k+1) (N := k+1) k).comp
        (f := Prod.snd) (x := (g,0)) analyticAt_snd
  have hOp : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1) =>
      cgOperator (matrixSequenceExtension (k+1) z.2.val.2 k)) (g,0) :=
    (matrixOperator_contDiffAt _ _ hP.contDiffAt).analyticAt
  have hs : AnalyticAt ℝ (fun z : EuclideanSpace ℝ (Fin (k+1)) × symmetricScenarios (k+1) (k+1) =>
      rfcsReferenceStep base z.1) (g,0) := by
    simpa only [Function.comp_def] using
      (rfcsReferenceStep_analytic base hb g hN).comp (f := Prod.fst)
        (x := (g,(0 : symmetricScenarios (k+1) (k+1)))) analyticAt_fst
  exact analytic_operator_apply hOp hs

end
end krylov.Correction
