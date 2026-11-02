import krylov.Cancellation.DeferredDataBudgetTaylor
import krylov.Cancellation.DeferredFullProfile
import krylov.Stability.UniformSupRemainder
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original true worst-output sharp expansion.
Use: derive the literal nonlinear canonical-gradient supremum over every
real symmetric source matrix budget with the exact printed sharp coefficient
and one genuine uniform quadratic remainder.
Source: actual uniform matrix-budget vector expansion, genuinely attained
physical linear matrix maximum and the proved real supremum transfer lemma.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The literal original sharp deferred error-profile coefficient.
Use: state source budget comparisons and sharp worst-output expansions compactly.
Article: main_krylov, thm:DC, printed sharp square-root profile. -/
def deferredSharpCoefficient (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (epsilon : ℝ) (omega : ℕ → ℝ) : ℝ :=
  ∑ l∈range k,omega l*Real.sqrt (‖cgCanonicalError base g k‖^2+
    epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2))

/-- The true canonical final-gradient norm supremum of original observed-estimate
DC over the actual original symmetric matrix increment budget class.
Use: the nonlinear source quantity is defined by the real original executor.
Article: main_krylov, thm:DC, actual worst output. -/
def deferredWorstOutput (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (omega : ℕ → ℝ) : ℝ :=
  sSup {z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
    (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧
    z=‖cgOperator (metricRoot base)⁻¹ (probedGradient (deferredDataMethod fullMemory (k+1) estimate)
      (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1))‖}

/-- The original actual deferred output supremum has exactly the printed
sharp error-profile coefficient and one true quadratic matrix-budget remainder.
Use: the source supremum is over real original symmetric matrix sequences;
no nonlinear maximizer, response expansion or independent remainder is assumed.
Article: main_krylov, thm:DC, exact original sharp supremum expansion.
Proof: the actual uniform native vector expansion is valid before choosing
the source budget or its matrices. The original linear matrix response has
its proved attained sharp maximum. True supremum transfer bounds the actual
nonlinear supremum on both sides by exactly that uniform quadratic remainder. -/
theorem deferred_data_sharp_budget_expansion
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
    let epsilon := 1-CG.length Q g k/a0
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) →
      (∑ l∈range k,omega l)≤delta →
      |sSup {z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
        (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧
        z=‖cgOperator (metricRoot base)⁻¹
          (probedGradient m (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1))‖}-
        (∑ l∈range k,omega l*Real.sqrt (‖cgCanonicalError base g k‖^2+
          epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2)))|≤
            C*(∑ l∈range k,omega l)^2 := by
  let Q := cgOperator base
  let m := deferredDataMethod fullMemory (k+1) estimate
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) g k)
  let epsilon := 1-CG.length Q g k/a0
  obtain ⟨delta,C,hd,hC,hbound⟩ := deferred_data_budget_expansion estimate base hb g k hcount hfull ha ha0
  refine ⟨delta,C,hd,hC,?_⟩
  intro omega homega hsmall
  let K := {E : ℕ → Matrix (Fin n) (Fin n) ℝ | (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l)}
  let f := fun E => cgOperator (metricRoot base)⁻¹
    (probedGradient m (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1))
  let L := deferredResponse base g k epsilon
  let c := ∑ l∈range k,omega l*Real.sqrt (‖cgCanonicalError base g k‖^2+
    epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2))
  have hstop : referenceAtomCount base hb g=k+1 := by omega
  have hsharp := deferred_full_response_sharp base hb g k hstop epsilon omega homega
  have hL : IsGreatest ((fun E => ‖L E‖) '' K) c := by
    constructor
    · obtain ⟨E,hE,hbudget,hvalue⟩ := hsharp.1
      exact ⟨E,⟨hE,hbudget⟩,hvalue.symm⟩
    · rintro z ⟨E,⟨hE,hbudget⟩,rfl⟩
      exact hsharp.2 ⟨E,hE,hbudget,rfl⟩
  have hs := sup_norm_remainder f L K c (C*(∑ l∈range k,omega l)^2) hL
    (fun E hE => hbound omega homega hsmall E hE.1 hE.2)
  have hset : ((fun E => ‖f E‖) '' K)={z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
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
