import krylov.Correction.RFCSCanonical
import krylov.Correction.ScenarioExpansion

/-!
Article: main_krylov, thm:RFCS, sharp actual finite-source probe bound.
Use: one real quadratic remainder tube covers every original finite
increment and independent probe-defect scenario; actual final isotropic
probe witnesses attain the sharp first-order coefficient.
Source: genuine independent-probe execution and full terminal expansion,
actual finite symmetric source coordinates and original spectral budgets.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Envelope krylov.Variation
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {k : ℕ}

/-- The actual final evaluated RFC-S gradient for a genuine finite symmetric increment/probe-defect scenario.
Use: both physical line and evaluated correction segments share their original source operator; only the measured probes have independent defects.
Article: main_krylov, thm:RFCS, actual finite-source output. -/
def rfcsScenarioOutput (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : symmetricScenarios (k+1) (k+1)) : EuclideanSpace ℝ (Fin (k+1)) :=
  let E := matrixSequenceExtension k Θ.val.1
  let P := matrixSequenceExtension (k+1) Θ.val.2
  rfcSGradient fullMemory (rfcsCanonicalProbe base E P) (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1)

/-- One genuine quadratic remainder tube bounds the actual RFC-S terminal expansion jointly over all original finite symmetric increment and independent probe-defect coordinates.
Use: constants precede every original budget profile and every scenario, with no supplied trajectory or residual expansion.
Article: main_krylov, thm:RFCS, actual all-source quadratic remainder.
Proof: original finite coordinate maps are analytic, have true zero
reference values and give exactly the genuine independently probed executor.
Apply its proved last-probe expansion in that complete actual source space;
unpack its genuine norm neighborhood once before every source scenario. -/
theorem rfcs_scenario_quadratic_tube (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖≤δ →
      ‖cgOperator (krylov.Secant.metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)-
        ‖canonicalCGStep base g k‖ • cgOperator (matrixSequenceExtension (k+1) Θ.val.2 k) (canonicalCGUnitStep base g k)‖≤C*‖Θ‖^2 := by
  -- All original source perturbations are genuine independent coordinates of this single actual executor tube.
  have ho := full_rfcs_canonical_first_order base hb g hN hk
    (fun Θ : symmetricScenarios (k+1) (k+1) => matrixSequenceExtension k Θ.val.1)
    (fun Θ => matrixSequenceExtension (k+1) Θ.val.2)
    symmetricScenario_increment_analytic symmetricScenario_correction_analytic
    (fun i => matrixSequenceExtension_zero k i) (fun i => matrixSequenceExtension_zero (k+1) i)
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp ho
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨ε/2,C,half_pos hε,hC,?_⟩
  intro Θ hΘ
  have ht := hεbound (by simpa only [dist_zero_right] using hΘ.trans_lt (half_lt_self hε))
  simpa only [rfcsScenarioOutput,Real.norm_of_nonneg (sq_nonneg ‖Θ‖)] using ht



end
end krylov.Correction
