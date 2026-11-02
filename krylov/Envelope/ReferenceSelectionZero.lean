import krylov.Methods.ReferenceSmoothClass
import krylov.Envelope.TargetedScenarioZero

set_option autoImplicit false
/-!
Article: Proposition B.18 [apB:prop:consist] of krylov.tex.
Use: close the genuine counterexample and zero infimum for the precise primitive smooth information class consistent only on the chosen reference.
Source: the actual targeted one-correction reference-class member, genuine zero response on all finite source scenarios and true worst-variation compact maxima.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual reference-only primitive smooth information class contains a genuine one-correction method with true worst transverse variation zero.
Use: The actual reference-only primitive smooth information class contains a genuine one-correction method with true worst transverse variation zero.
Article: main_krylov, apB:prop:consist, actual attained zero value without global consistency.
Proof: Use the real targeted primitive implementation and its proved actual zero response on every source scenario. -/
theorem reference_selection_zero_attained
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g) (ω : Fin ((k+1)-1) → ℝ≥0) :
    ∃ M : ReferenceSmoothProbedClass (EuclideanSpace ℝ (Fin n)) (cgOperator base) g (k+1),
      OneCorrectionMethod M.policy ∧ worstTransverse M.policy base g (k+1) ω=0 := by
  let M := targetedReferenceClass (cgOperator base) (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g (k+1)
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))
  exact ⟨M,targetedFinalMethod_oneCorrection (k+1) _,targeted_worstTransverse_zero base hb g k hcount ω⟩

/-- Zero is the genuine attained minimum worst variation in the actual reference-only primitive smooth class.
Use: Zero is the genuine attained minimum worst variation in the actual reference-only primitive smooth class.
Article: main_krylov, apB:prop:consist, actual attained zero value without global consistency.
Proof: The real targeted method attains zero and every actual worst variation is nonnegative because its genuine zero scenario is feasible. -/
theorem reference_selection_isLeast_zero
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g) (ω : Fin ((k+1)-1) → ℝ≥0) :
    IsLeast {v : ℝ | ∃ M : ReferenceSmoothProbedClass (EuclideanSpace ℝ (Fin n)) (cgOperator base) g (k+1),
      worstTransverse M.policy base g (k+1) ω=v} 0 := by
  obtain ⟨M,_,hM⟩ := reference_selection_zero_attained base hb g k hcount ω
  refine ⟨⟨M,hM⟩,?_⟩
  rintro v ⟨L,hL⟩
  rw [← hL]
  apply (worstTransverse_attained L.policy base g (k+1) ω).2
  refine ⟨0,scenarioBudget_zero_mem ω,?_⟩
  simp only [map_zero,norm_zero]

/-- The genuine infimum of actual worst transverse variations in the precise reference-only primitive smooth class is exactly zero.
Use: The genuine infimum of actual worst transverse variations in the precise reference-only primitive smooth class is exactly zero.
Article: main_krylov, apB:prop:consist, actual attained zero value without global consistency.
Proof: Use the actual attained least-value theorem, including every genuine degenerate source budget. -/
theorem reference_selection_infimum_zero
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g) (ω : Fin ((k+1)-1) → ℝ≥0) :
    sInf {v : ℝ | ∃ M : ReferenceSmoothProbedClass (EuclideanSpace ℝ (Fin n)) (cgOperator base) g (k+1),
      worstTransverse M.policy base g (k+1) ω=v}=0 :=
  (reference_selection_isLeast_zero base hb g k hcount ω).csInf_eq
end
end krylov.Envelope
