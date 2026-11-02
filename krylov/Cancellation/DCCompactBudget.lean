import krylov.Cancellation.DCCompactScenario
import krylov.Stability.FiniteScenarioBudget
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), original compact C-one matrix-budget expansion.
Use: cover all original infinite symmetric increment matrices and budgets
with one true native output remainder and the original initial-error weight.
Source: proved genuine compact C-one source expansion and the exact reused
finite source-prefix and matrix-budget transfer dictionary.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Set Filter krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Every original symmetric matrix-budget scenario of consistent native
DC-slide has the same genuine weighted quadratic full-vector remainder,
uniformly over the original compact reference family, under C-one data.
Use: the radius and constant precede all references, matrix sequences and
budgets; native full-vector source uniformity is proved, not assumed.
Article: main_krylov, apH:dcs2(b), full original matrix-budget uniformity.
Proof: the genuine native finite-source expansion gives its common weighted
remainder. The exact reused finite-prefix dictionary preserves the actual
original execution and calibrated response on every infinite source sequence,
while its genuine finite source norm is at most the original summed budget. -/
theorem dc_slide_consistent_compact_budget_expansion
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hfull : k+1=n) (K : Set X) (hK : IsCompact K)
    (hbsym : ∀ x,(base x).IsSymm)
    (hb : ∀ x∈K,ContDiffAt ℝ 1 base x) (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hg : ∀ x∈K,ContDiffAt ℝ 1 g x)
    (hcount : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (ha : ∀ x∈K,∀ j<n,
      let Q := cgOperator (base x)
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => Q) (fun _ => Q) (g x) j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ x∈K,∀ j<n,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j))
    (hcal : ∀ x∈K,∀ j<n,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator (base x)) (fun _ => cgOperator (base x)) (g x) j)=CG.length (cgOperator (base x)) (g x) j) :
    let m := dcSlideMethod fullMemory estimate
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) →
      (∑ l∈range k,omega l)≤delta →
      ∀ E : ℕ → Matrix (Fin n) (Fin n) ℝ,(∀ l,(E l).IsSymm) → (∀ l<k,‖E l‖≤omega l) →
      let R := cgOperator (metricRoot (base x))⁻¹
      ‖R (probedGradient m (canonicalFCPath (base x) E 1) (canonicalFCPath (base x) E 1) (g x) (k+1))-
        deferredResponse (base x) (g x) k 0 E‖≤C*(∑ l∈range k,omega l)^2*‖R (g x)‖ := by
  let m := dcSlideMethod fullMemory estimate
  obtain ⟨delta,C,hd,hC,hbound⟩ := dc_slide_consistent_compact_scenario_expansion estimate base g k hfull K hK
    hbsym hb hpos hg hcount ha ha0 hcal
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx omega homega hsmall E hE hbudget
  let R := cgOperator (metricRoot (base x))⁻¹
  have hlocal := finite_scenario_budget_transfer (base x) (g x) k m R
    (deferredResponse (base x) (g x) k 0)
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
