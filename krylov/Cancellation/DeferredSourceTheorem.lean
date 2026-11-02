import krylov.Cancellation.DeferredDataSharpExpansion
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, literal full source sharp worst-output theorem.
Use: state the real nonlinear budget supremum expansion using one common
quadratic bound in the original largest source budget scale.
Source: actual native uniform sharp budget expansion and finite budget
comparison; every response, maximizer and remainder has been proved earlier.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original full-cycle observed-estimate DC worst output equals the
literal printed sharp coefficient up to one genuine uniform largest-budget
quadratic remainder, including all zero budgets.
Use: this is the original nonlinear supremum statement, with its radius and
constant chosen before every admitted source budget and actual matrix scenario.
Article: main_krylov, thm:DC, full sharp O(omega squared) source conclusion.
Proof: the proved actual sharp supremum expansion has one uniform quadratic
sum-budget remainder. The finite sum is at most the horizon times the original
largest budget; choose the common radius before that scale and absorb only
this fixed finite horizon factor into the true common quadratic constant. -/
theorem deferred_data_sharp_expansion
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
    let epsilon := 1-CG.length Q g k/a0
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ omegaBar : ℝ,0≤omegaBar → omegaBar≤delta →
      ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) → (∀ l<k,omega l≤omegaBar) →
      |deferredWorstOutput estimate base g k omega-deferredSharpCoefficient base g k epsilon omega|≤C*omegaBar^2 := by
  let Q := cgOperator base
  let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
  let epsilon := 1-CG.length Q g k/a0
  obtain ⟨delta0,C0,hd,hC,hbound⟩ := deferred_data_sharp_budget_expansion estimate base hb g k hcount hfull ha ha0
  let A : ℝ := (k : ℝ)+1
  have hA : 0<A := by dsimp only [A];positivity
  refine ⟨delta0/A,C0*A^2,div_pos hd hA,by positivity,?_⟩
  intro omegaBar hbar hsmall omega homega hbudget
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
  have he := hbound omega homega hsmallW
  change |deferredWorstOutput estimate base g k omega-deferredSharpCoefficient base g k epsilon omega|≤C0*W^2 at he
  calc
    _≤C0*W^2 := he
    _≤C0*(A*omegaBar)^2 := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hW (mul_nonneg hA.le hbar)).mpr hsum) hC
    _=(C0*A^2)*omegaBar^2 := by ring

end
end krylov.Cancellation
