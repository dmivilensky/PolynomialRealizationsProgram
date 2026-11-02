import krylov.OneGradient.KnownBaseTwoQueryScenario
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), exact whole-scenario guarantee equivalence.
Use: the genuine all-M1 two-query minimax covers precisely the preexisting
original zero-prior physical admissibility class, with actual execution.
Source: exact known-base reconstruction, genuine scenario realization
and literal complete two-query history and output dictionaries.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Information

/-- The original full physical two-query guarantee is equivalent to a
uniform bound on every preexisting original admissible zero-prior scenario,
using its actual probe oracle, complete history and unevaluated output.
Use: the exact known-base M1 minimax has the original source quantifiers;
no hidden restriction to a canonical game or special matrix family remains.
Article: main_krylov, thm:local(c), whole original scenario equivalence.
Proof: zero prior fixes the actual base. The genuine first increment and
independent terminal form give exactly the two physical budgets and true
two-query execution. Conversely realize each arbitrary budgeted matrix
pair as its actual admissible original scenario and identify its output. -/
theorem knownBaseTwoQueryGuarantee_iff_scenarios
    (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (eta radius v : ℝ)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2))) :
    knownBaseTwoQueryGuarantee base g eta radius m v ↔
      ∀ S : Scenario 2,S.Admissible 1 base 0 (fun _ => eta) radius 0 →
        ‖cgOperator (metricRoot base)⁻¹ (m.outputGradient (cgOperator (S.lastOperator 1))
          (oneGradientRun m S.probeOracle g 2))‖≤‖cgCanonicalError base g 1‖*v := by
  constructor
  · intro hguarantee S hS
    have hbase : S.base=base := knownBase_zero_prior_eq base S.base hb hS.2.1
    have hinc := hS.2.2.1 0 (by decide : 0<1)
    have hC : (S.probe 1).IsSymm := by
      simpa only [Scenario.probe,Finset.sum_range_one] using hS.1.isHermitian.isSymm.add hinc.1
    have hB : (S.lastOperator 1).IsSymm := hC.add hS.2.2.2.1
    have hbudget : relativeBudget base (S.probe 1-base)≤ eta := by
      simpa only [Scenario.probe,Finset.sum_range_one,hbase,add_sub_cancel_left] using hinc.2
    have houtput : relativeBudget base (S.lastOperator 1-S.probe 1)≤ radius := by
      simpa only [Scenario.lastOperator,add_sub_cancel_left,hbase] using hS.2.2.2.2.1
    rw [knownBaseTwoQueryScenario_histories S base hbase m g]
    exact hguarantee (S.probe 1) hC hbudget (S.lastOperator 1) hB houtput
  · intro hscenarios C hC hbudget B hB houtput
    let S := knownBaseTwoQueryScenario base C B
    have hp : S.probe 1=C := by
      dsimp only [S,knownBaseTwoQueryScenario,Scenario.probe]
      rw [Finset.sum_range_one]
      abel
    have hl : S.lastOperator 1=B := by
      change S.probe 1+(B-C)=B
      rw [hp]
      abel
    have hhistory : oneGradientRun m S.probeOracle g 2=
        oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2 := by
      rw [knownBaseTwoQueryScenario_histories S base rfl m g,hp]
    have h := hscenarios S (knownBaseTwoQueryScenario_admissible base C B hb hC hB eta radius hbudget houtput)
    rw [hl,hhistory] at h
    exact h

end
end krylov.OneGradient
