import krylov.Cancellation.DCCompactBudget
import krylov.Cancellation.DeferredDataSharpExpansion
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), original compact-uniform sharp native cycle.
Use: close the true nonlinear original worst-output statement for consistent
DC-slide under C-one data with the literal correction-free minimax coefficient.
Source: genuine native compact C-one matrix-budget vector remainder, actual
attained symmetric fresh maximum and the proved real supremum transfer.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset Set Filter krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped Topology BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The actual original full-cycle DC-slide worst canonical gradient norm
on the genuine symmetric source increment budget class.
Use: the source supremum is defined by the real executor.
Article: main_krylov, apH:dcs2(b), actual native worst output. -/
def dcSlideWorstOutput (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (omega : ℕ → ℝ) : ℝ :=
  sSup {z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
    (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧
    z=‖cgOperator (metricRoot base)⁻¹ (probedGradient (dcSlideMethod fullMemory estimate)
      (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1))‖}

/-- The true nonlinear consistent DC-slide supremum has exactly the original
correction-free minimax coefficient W0 times the true last-error norm and one
common weighted quadratic remainder in the largest-budget scale, uniformly
before every compact reference, matrix sequence and budget, under C-one data.
Use: this closes native full-vector sharp uniformity, including all zero
budgets; no output response, nonlinear maximizer or uniformity field is assumed.
Article: main_krylov, apH:dcs2(b), full original compact-uniform sharp cycle.
Proof: the actual compact C-one vector remainder is already derived from
native residuals and genuine moving-basis reconstruction. Bound the finite
budget sum by the fixed horizon times the largest budget. The real symmetric
calibrated response maximum is attained and equals the printed minimax value.
True supremum transfer gives both sides of the nonlinear original supremum
bound with exactly that same common quadratic remainder. -/
theorem dc_slide_consistent_compact_sharp_expansion
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
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ omegaBar : ℝ,0≤omegaBar → omegaBar≤delta →
      ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) → (∀ l<k,omega l≤omegaBar) →
      let R := cgOperator (metricRoot (base x))⁻¹
      |dcSlideWorstOutput estimate (base x) (g x) k omega-
        (∑ l∈range k,omega l)*‖cgCanonicalError (base x) (g x) k‖|≤C*omegaBar^2*‖R (g x)‖ := by
  let m := dcSlideMethod fullMemory estimate
  obtain ⟨delta0,C0,hd,hC,hbound⟩ := dc_slide_consistent_compact_budget_expansion estimate base g k hfull K hK hbsym hb hpos hg hcount ha ha0 hcal
  let A : ℝ := (k : ℝ)+1
  have hA : 0<A := by dsimp only [A];positivity
  refine ⟨delta0/A,C0*A^2,div_pos hd hA,by positivity,?_⟩
  intro x hx omegaBar hbar hsmall omega homega hbudget
  let R := cgOperator (metricRoot (base x))⁻¹
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
  let L := deferredResponse (base x) (g x) k 0
  let c := W*‖cgCanonicalError (base x) (g x) k‖
  let r := (C0*A^2)*omegaBar^2*‖R (g x)‖
  have hN : k+1≤referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x) := by rw [hcount x hx];omega
  have hsharp := deferred_response_sharp (base x) (hpos x hx).self_of_nhds (g x) k hN 0 omega homega
  have hc : (∑ l∈range k,omega l*Real.sqrt (cgEnergy (base x) (g x) k+
      (0 : ℝ)^2*(‖cgCanonicalError (base x) (g x) (l+1)‖^2-‖cgCanonicalError (base x) (g x) k‖^2)))=c := by
    simp only [zero_pow (by decide : (2 : ℕ)≠0),zero_mul,add_zero]
    rw [← Finset.sum_mul,last_energy_error_norm (base x) (hpos x hx).self_of_nhds (g x) k (by rw [hcount x hx];omega)]
  rw [hc] at hsharp
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
