import krylov.Cancellation.DeferredDataCompact
import krylov.Stability.FiniteScenarioBudget
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, compact-uniform original infinite matrix budgets.
Use: transfer the genuine compact-reference finite-source expansion to all
original symmetric matrix sequences, with one common weighted remainder.
Source: proved actual compact native expansion and the exact reused finite
source-prefix/budget dictionary, including zero budgets and empty prefixes.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Set krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- One true common quadratic output remainder holds across every compact
full-atom reference family and every original infinite symmetric source
matrix sequence in its genuine budget ball.
Use: the radius and constant precede the reference, budgets and all actual
matrices, with the original true initial-error weight retained.
Article: main_krylov, thm:DC, compact-uniform actual matrix-budget expansion.
Proof: the genuine compact native scenario theorem supplies its common
radius and weighted constant. Apply the exact finite-source budget transfer
at each real reference; the actual deferred response respects the same true
prefix, so no new expansion or independent uniformity assumption is supplied. -/
theorem deferred_data_compact_budget_expansion
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K,ContDiffAt ℝ 2 base x)
    (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hg : ∀ x∈K,ContDiffAt ℝ 2 g x)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (ha : ∀ x∈K,
      let Q := cgOperator (base x)
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) (g x) k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) k)) :
    let m := deferredDataMethod fullMemory (k+1) estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) →
      (∑ l∈range k,omega l)≤delta →
      ∀ E : ℕ → Matrix (Fin n) (Fin n) ℝ,(∀ l,(E l).IsSymm) → (∀ l<k,‖E l‖≤omega l) →
      let Q := cgOperator (base x)
      let R := cgOperator (metricRoot (base x))⁻¹
      let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) (g x) k)
      ‖R (probedGradient m (canonicalFCPath (base x) E 1) (canonicalFCPath (base x) E 1) (g x) (k+1))-
        deferredResponse (base x) (g x) k (1-CG.length Q (g x) k/a0) E‖≤
          C*(∑ l∈range k,omega l)^2*‖R (g x)‖ := by
  let m := deferredDataMethod fullMemory (k+1) estimate
  obtain ⟨delta,C,hd,hC,hbound⟩ := deferred_data_compact_scenario_expansion estimate base g k hfull K hK hb hpos hg hcount ha ha0
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx omega homega hsmall E hE hbudget
  let Q := cgOperator (base x)
  let R := cgOperator (metricRoot (base x))⁻¹
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) (g x) k)
  let epsilon := 1-CG.length Q (g x) k/a0
  have hlocal := finite_scenario_budget_transfer (base x) (g x) k m R
    (deferredResponse (base x) (g x) k epsilon)
    (fun D E hDE => by
      unfold deferredResponse
      exact sum_congr rfl (fun l hl => by rw [hDE l (mem_range.mp hl)]))
    delta (C*‖R (g x)‖) (mul_nonneg hC (norm_nonneg _))
    (fun Theta hnorm hTheta => by
      have hh := hbound x hx Theta hnorm hTheta
      convert! hh using 1
      ring)
    omega homega hsmall E hE hbudget
  convert! hlocal using 1
  ring

end
end krylov.Cancellation
