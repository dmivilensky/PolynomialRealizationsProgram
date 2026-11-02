import krylov.Cancellation.DeferredDataCompactBudget
import krylov.Cancellation.DeferredDataSharpExpansion
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original compact-uniform sharp supremum theorem.
Use: bound the actual nonlinear worst output on both sides by the literal
sharp coefficient with one common maximal-budget quadratic remainder.
Source: genuine native compact matrix-budget vector expansion, attained
original symmetric matrix maximum and the proved true supremum transfer.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Set krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The true nonlinear original deferred worst-output supremum has the
literal sharp coefficient with one weighted quadratic remainder in the
original largest-budget scale, uniformly over every compact full-atom
reference family, all source budgets and all actual symmetric matrices.
Use: the radius and constant precede the reference and every original
source choice; no nonlinear maximizer or supplied uniform expansion is assumed.
Article: main_krylov, thm:DC, full original compact-uniform sharp conclusion.
Proof: derive the genuine common native matrix-budget vector remainder.
The finite budget sum is bounded by the fixed horizon times the original
largest budget. At every reference the original linear symmetric-matrix
maximum is genuinely attained, so true supremum transfer gives both sides
of the actual nonlinear supremum estimate with that same common remainder. -/
theorem deferred_data_compact_sharp_expansion
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
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ omegaBar : ℝ,0≤omegaBar → omegaBar≤delta →
      ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) → (∀ l<k,omega l≤omegaBar) →
      let Q := cgOperator (base x)
      let R := cgOperator (metricRoot (base x))⁻¹
      let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) (g x) k)
      |deferredWorstOutput estimate (base x) (g x) k omega-
        deferredSharpCoefficient (base x) (g x) k (1-CG.length Q (g x) k/a0) omega|≤C*omegaBar^2*‖R (g x)‖ := by
  let m := deferredDataMethod fullMemory (k+1) estimate
  obtain ⟨delta0,C0,hd,hC,hbound⟩ := deferred_data_compact_budget_expansion estimate base g k hfull K hK hb hpos hg hcount ha ha0
  let A : ℝ := (k : ℝ)+1
  have hA : 0<A := by dsimp only [A];positivity
  refine ⟨delta0/A,C0*A^2,div_pos hd hA,by positivity,?_⟩
  intro x hx omegaBar hbar hsmall omega homega hbudget
  let Q := cgOperator (base x)
  let R := cgOperator (metricRoot (base x))⁻¹
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) (g x) k)
  let epsilon := 1-CG.length Q (g x) k/a0
  let W := ∑ l∈range k,omega l
  have hW : 0≤W := sum_nonneg (fun l hl => homega l (mem_range.mp hl))
  have hsum : W≤A*omegaBar := by
    have hs : W≤(k : ℝ)*omegaBar := by
      calc
        _≤∑ _l∈range k,omegaBar := sum_le_sum (fun l hl => hbudget l (mem_range.mp hl))
        _=(k : ℝ)*omegaBar := by rw [sum_const,card_range,nsmul_eq_mul]
    dsimp only [A]
    linarith
  have hsmallW : W≤delta0 := hsum.trans (by
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hsmall)
  let S := {E : ℕ → Matrix (Fin n) (Fin n) ℝ | (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l)}
  let f := fun E => R (probedGradient m (canonicalFCPath (base x) E 1) (canonicalFCPath (base x) E 1) (g x) (k+1))
  let L := deferredResponse (base x) (g x) k epsilon
  let c := deferredSharpCoefficient (base x) (g x) k epsilon omega
  let r := (C0*A^2)*omegaBar^2*‖R (g x)‖
  have hstop : referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=k+1 := by rw [hcount x hx];omega
  have hsharp := deferred_full_response_sharp (base x) (hpos x hx).self_of_nhds (g x) k hstop epsilon omega homega
  have hL : IsGreatest ((fun E => ‖L E‖) '' S) c := by
    constructor
    · obtain ⟨E,hE,hbudget,hvalue⟩ := hsharp.1
      exact ⟨E,⟨hE,hbudget⟩,hvalue.symm⟩
    · rintro z ⟨E,⟨hE,hbudget⟩,rfl⟩
      exact hsharp.2 ⟨E,hE,hbudget,rfl⟩
  have hrem (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : E∈S) : ‖f E-L E‖≤r := by
    have he := hbound x hx omega homega hsmallW E hE.1 hE.2
    change ‖f E-L E‖≤C0*W^2*‖R (g x)‖ at he
    calc
      _≤C0*W^2*‖R (g x)‖ := he
      _≤C0*(A*omegaBar)^2*‖R (g x)‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hW (mul_nonneg hA.le hbar)).mpr hsum) hC) (norm_nonneg _)
      _=r := by dsimp only [r];ring
  have hs := sup_norm_remainder f L S c r hL hrem
  have hset : ((fun E => ‖f E‖) '' S)={z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧ z=‖f E‖} := by
    ext z
    constructor
    · rintro ⟨E,⟨hE,hbudget⟩,hvalue⟩
      exact ⟨E,hE,hbudget,hvalue.symm⟩
    · rintro ⟨E,hE,hbudget,hvalue⟩
      exact ⟨E,⟨hE,hbudget⟩,hvalue.symm⟩
  rw [hset] at hs
  exact hs

end
end krylov.Cancellation
