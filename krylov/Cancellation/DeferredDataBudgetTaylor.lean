import krylov.Cancellation.DeferredDataScenarioTaylor
import krylov.Stability.FiniteScenarioBudget
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, actual uniform original matrix-budget expansion.
Use: transfer the real joint finite-scenario remainder to every original
infinite matrix sequence with the same true finite source budget, using the
actual executor and genuine source-prefix dictionary.
Source: proved uniform finite-scenario Taylor expansion, exact real prefix
nonanticipation, actual zero correction slots and true finite norm inequalities.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original actual deferred output has one uniform quadratic vector
remainder over every true symmetric matrix budget sequence near zero.
Use: constants are chosen before the source budget and its real matrices;
the original infinite matrix sequence is not replaced by an assumed response.
Article: main_krylov, thm:DC, genuine uniform matrix-budget O(omega squared).
Proof: retain the genuine finite source increment coordinates with zero
correction slots. Their real norm is bounded by the sum of the original
budgets. Exact prefix equality identifies the original actual execution and
spatial response with this true finite scenario. Apply its proved common
quadratic remainder and the genuine finite norm bound. -/
theorem deferred_data_budget_expansion
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha :
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)) :
    let Q := cgOperator base
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let m := deferredDataMethod fullMemory (k+1) estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) →
      (∑ l∈range k,omega l)≤delta →
      ∀ E : ℕ → Matrix (Fin n) (Fin n) ℝ,(∀ l,(E l).IsSymm) → (∀ l<k,‖E l‖≤omega l) →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1))-
        deferredResponse base g k (1-CG.length Q g k/a0) E‖≤C*(∑ l∈range k,omega l)^2 := by
  let Q := cgOperator base
  let m := deferredDataMethod fullMemory (k+1) estimate
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) g k)
  let epsilon := 1-CG.length Q g k/a0
  obtain ⟨delta,C,hd,hC,hbound⟩ := deferred_data_scenario_expansion estimate base hb g k hcount hfull ha ha0
  refine ⟨delta,C,hd,hC,?_⟩
  exact finite_scenario_budget_transfer base g k m (cgOperator (metricRoot base)⁻¹)
    (deferredResponse base g k epsilon)
    (fun D E hDE => by
      unfold deferredResponse
      exact sum_congr rfl (fun l hl => by rw [hDE l (mem_range.mp hl)]))
    delta C hC hbound

end
end krylov.Cancellation
