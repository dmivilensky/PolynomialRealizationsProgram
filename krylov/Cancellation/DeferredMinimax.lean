import krylov.Cancellation.CorrectionFreeBudgetWitness
import krylov.Cancellation.DeferredComparison
import krylov.Cancellation.DeferredDataFirstVariation
import krylov.Methods.DeferredSmoothClass
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, attained original correction-free first-order minimax.
Use: optimize the actual full-cycle canonical gradient first variation over
all genuine primitive smooth correction-free source methods and real original
symmetric matrix budget scenarios.
Source: one universal actual hidden-prefix budget witness, native calibrated
DC source-class membership and the proved true sharp deferred response bound.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Supplied with the true last reference line length, the actual calibrated
DC implementation attains the exact original correction-free first-order
minimax value over every primitive smooth source method.
Use: the minimizing method and forcing matrix scenarios are genuinely
constructed; no optimal method, response or minimax equality is assumed.
Article: main_krylov, thm:DC, minimum W0 times square-root last energy.
Proof: the genuine constant-calibrated deferred method belongs to the original
primitive smooth globally CG-consistent correction-free class. Its actual
first derivative is the proved literal zero-damping deferred response, whose
sharp matrix bound is exactly the printed value. Conversely one real symmetric
budget scenario forces that very derivative norm on every actual correction-free
CG-consistent executor, so every admitted uniform coefficient is at least this value. -/
theorem correction_free_first_order_minimax
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : 0<k) (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    IsLeast {C : ℝ | ∃ M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)),
      Methods.CorrectionFree M.policy ∧
      ∀ E : ℕ → Matrix (Fin n) (Fin n) ℝ,(∀ l,(E l).IsSymm) → (∀ l<k,‖E l‖≤omega l) →
      ‖deriv (fun t : ℝ => cgOperator (metricRoot base)⁻¹
        (probedGradient M.policy (canonicalFCPath base E t) (fun _ => cgOperator base) g (k+1))) 0‖≤C}
      (Real.sqrt (cgEnergy base g k)*(∑ l∈Finset.range k,omega l)) := by
  let Q := cgOperator base
  let a := CG.length Q g k
  have hN : k+1≤referenceAtomCount base hb g := by omega
  have ha : 0<a := cgLength_pos base hb g k (by omega)
  constructor
  · let M := smoothDeferredClass fullMemory (fun _ hj => hj) (k+1) a (E := EuclideanSpace ℝ (Fin n))
    refine ⟨M,deferredMethod_correctionFree fullMemory (k+1) a,?_⟩
    intro E hE hbudget
    have hchart :
        let H := methodRun (deferredDataMethod fullMemory (k+1) (fun _ => a)) (fun _ => Q) (fun _ => Q) g k
        ContDiffAt ℝ 2 (historyEstimateChart (fun _ => a) H.queryShape H.observationList.length)
          (observedArray H.observationList.length H.observationList) := contDiffAt_const
    have hd := deferred_data_full_hasDerivAt (fun _ => a) base hb g E hE (fun _ _ => Q) k
      (fun _ _ => contDiffAt_const) rfl hcount hfull hchart ha
    change HasDerivAt (fun t : ℝ => cgOperator (metricRoot base)⁻¹
      (probedGradient M.policy (canonicalFCPath base E t) (fun _ => Q) g (k+1)))
      (deferredResponse base g k (1-a/a) E) 0 at hd
    rw [div_self ha.ne',sub_self] at hd
    rw [hd.deriv]
    have hu := deferred_response_le base g k 0 E omega hbudget
    rw [deferred_calibrated_constant base hb g k omega] at hu
    simpa only [mul_comm] using hu
  · rintro C ⟨M,hfree,hbound⟩
    obtain ⟨E,hE,hbudget,hforce⟩ := correction_free_budget_witness base hb g k hk hN omega homega
    have hd := hforce M.policy M.consistent hfree (fun _ _ => Q)
    have he : ‖deriv (fun t : ℝ => cgOperator (metricRoot base)⁻¹
        (probedGradient M.policy (canonicalFCPath base E t) (fun _ => Q) g (k+1))) 0‖=
        Real.sqrt (cgEnergy base g k)*(∑ l∈Finset.range k,omega l) := by
      rw [hd.deriv,norm_smul,Real.norm_eq_abs,(firstStep_common base hb g (by omega)).1,mul_one,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun l hl => homega l (Finset.mem_range.mp hl))))]
    rw [← he]
    exact hbound E hE hbudget

end
end krylov.Cancellation
