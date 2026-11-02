import krylov.Envelope.SelectionInformationBound
import krylov.Envelope.RFCSelectionValue
import krylov.Methods.CorrectionCount

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, actual attained smooth-class transverse minimax.
Use: prove the genuine minimax equality for the complete smooth globally
CG-consistent information class and its true one-correction subclass.
Source: constructed actual absorbed forcing scenarios and the real
one-correction full-memory RFC primitive class and worst-scenario equality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The selection value is the attained minimum of the actual worst transverse variation over the entire genuine smooth globally CG-consistent source information class.
Use: The selection value is the attained minimum of the actual worst transverse variation over the entire genuine smooth globally CG-consistent source information class.
Article: main_krylov, thm:select, actual attained smooth-class transverse minimax.
Proof: The actual absorbed forcing scenario bounds every class member below. The genuine primitive smooth RFC class supplies a real minimizer. -/
theorem selection_minimax (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    IsLeast (Set.range (fun M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)) =>
      worstTransverse M.policy base g N ω)) (selectionValue base g N ω) := by
  refine ⟨?_,?_⟩
  · refine ⟨smoothRFCClass fullMemory (fun _ hk => hk) 1,?_⟩
    exact rfc_worstTransverse_eq_selectionValue base hb g N hN hcount ω
  · rintro r ⟨M,rfl⟩
    exact selection_le_worstTransverse M base hb g N hN hcount ω

/-- The same genuine selection value is the attained minimum in the actual at-most-one-correction-per-iteration smooth source subclass.
Use: The same genuine selection value is the attained minimum in the actual at-most-one-correction-per-iteration smooth source subclass.
Article: main_krylov, thm:select, actual attained smooth-class transverse minimax.
Proof: Use the true one-correction RFC class witness and the actual forcing lower bound for every smooth globally CG-consistent method. -/
theorem selection_oneCorrection_minimax (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    IsLeast ((fun M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)) =>
      worstTransverse M.policy base g N ω) '' {M | OneCorrectionMethod M.policy})
      (selectionValue base g N ω) := by
  refine ⟨?_,?_⟩
  · refine ⟨smoothRFCClass fullMemory (fun _ hk => hk) 1,rfcMethod_oneCorrection fullMemory,?_⟩
    exact rfc_worstTransverse_eq_selectionValue base hb g N hN hcount ω
  · rintro r ⟨M,_,rfl⟩
    exact selection_le_worstTransverse M base hb g N hN hcount ω
end
end krylov.Envelope
