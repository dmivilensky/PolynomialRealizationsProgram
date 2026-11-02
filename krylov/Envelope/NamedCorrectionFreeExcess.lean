import krylov.Envelope.CorrectionFreeExcess
import krylov.Methods.CorrectionFreeClasses

set_option autoImplicit false
/-!
Article: main_krylov, s3:cor:qn, genuine named correction-free strict separation.
Use: obtain the actual excess bound and strict minimax separation for HS, HZ, positive scalar-initialized BFGS/L-BFGS and every positive newest-pair FC window.
Source: complete genuine primitive smooth correction-free class memberships and the proved universal actual excess theorem.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Actual Hestenes-Stiefel has the printed worst-variation excess and strict separation for positive final budget.
Use: Actual Hestenes-Stiefel has the printed worst-variation excess and strict separation for positive final budget.
Article: main_krylov, s3:cor:qn, genuine named correction-free strict separation.
Proof: Apply the universal genuine correction-free excess bound and its strict positive-newest-budget consequence to the actual primitive smooth implementation. -/
theorem hs_excess
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2)≤
      worstTransverse (smoothHSClass (E := EuclideanSpace ℝ (Fin n))).policy base g N ω ∧
    (0<ω ⟨N-2,by omega⟩ → selectionValue base g N ω<worstTransverse (smoothHSClass (E := EuclideanSpace ℝ (Fin n))).policy base g N ω) :=
  ⟨correctionFree_excess_lower (smoothHSClass (E := EuclideanSpace ℝ (Fin n))) smoothHSClass_correctionFree base hb g N hN hcount ω,
    correctionFree_strict_excess (smoothHSClass (E := EuclideanSpace ℝ (Fin n))) smoothHSClass_correctionFree base hb g N hN hcount ω⟩

/-- Actual Hager-Zhang has the printed worst-variation excess and strict separation for positive final budget.
Use: Actual Hager-Zhang has the printed worst-variation excess and strict separation for positive final budget.
Article: main_krylov, s3:cor:qn, genuine named correction-free strict separation.
Proof: Apply the universal genuine correction-free excess bound and its strict positive-newest-budget consequence to the actual primitive smooth implementation. -/
theorem hz_excess
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2)≤
      worstTransverse (smoothHZClass (E := EuclideanSpace ℝ (Fin n))).policy base g N ω ∧
    (0<ω ⟨N-2,by omega⟩ → selectionValue base g N ω<worstTransverse (smoothHZClass (E := EuclideanSpace ℝ (Fin n))).policy base g N ω) :=
  ⟨correctionFree_excess_lower (smoothHZClass (E := EuclideanSpace ℝ (Fin n))) smoothHZClass_correctionFree base hb g N hN hcount ω,
    correctionFree_strict_excess (smoothHZClass (E := EuclideanSpace ℝ (Fin n))) smoothHZClass_correctionFree base hb g N hN hcount ω⟩

/-- Every actual positive-scalar-initialized L-BFGS method with a positive newest-pair memory has the printed excess and strict separation.
Use: Every actual positive-scalar-initialized L-BFGS method with a positive newest-pair memory has the printed excess and strict separation.
Article: main_krylov, s3:cor:qn, genuine named correction-free strict separation.
Proof: Apply the universal genuine correction-free excess bound and its strict positive-newest-budget consequence to the actual primitive smooth implementation. -/
theorem lbfgs_excess (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k) (c : ℝ) (hc : 0<c)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2)≤
      worstTransverse (smoothLBFGSClass (E := EuclideanSpace ℝ (Fin n)) memory hm c hc).policy base g N ω ∧
    (0<ω ⟨N-2,by omega⟩ → selectionValue base g N ω<worstTransverse (smoothLBFGSClass (E := EuclideanSpace ℝ (Fin n)) memory hm c hc).policy base g N ω) :=
  ⟨correctionFree_excess_lower (smoothLBFGSClass (E := EuclideanSpace ℝ (Fin n)) memory hm c hc) (smoothLBFGSClass_correctionFree memory hm c hc) base hb g N hN hcount ω,
    correctionFree_strict_excess (smoothLBFGSClass (E := EuclideanSpace ℝ (Fin n)) memory hm c hc) (smoothLBFGSClass_correctionFree memory hm c hc) base hb g N hN hcount ω⟩

/-- Every actual positive newest-pair FC window has the printed excess and strict separation.
Use: Every actual positive newest-pair FC window has the printed excess and strict separation.
Article: main_krylov, s3:cor:qn, genuine named correction-free strict separation.
Proof: Apply the universal genuine correction-free excess bound and its strict positive-newest-budget consequence to the actual primitive smooth implementation. -/
theorem fc_excess (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2)≤
      worstTransverse (smoothFCClass (E := EuclideanSpace ℝ (Fin n)) memory hm).policy base g N ω ∧
    (0<ω ⟨N-2,by omega⟩ → selectionValue base g N ω<worstTransverse (smoothFCClass (E := EuclideanSpace ℝ (Fin n)) memory hm).policy base g N ω) :=
  ⟨correctionFree_excess_lower (smoothFCClass (E := EuclideanSpace ℝ (Fin n)) memory hm) (smoothFCClass_correctionFree memory hm) base hb g N hN hcount ω,
    correctionFree_strict_excess (smoothFCClass (E := EuclideanSpace ℝ (Fin n)) memory hm) (smoothFCClass_correctionFree memory hm) base hb g N hN hcount ω⟩

/-- Actual positive-scalar-initialized BFGS has the printed excess and strict separation.
Use: Actual positive-scalar-initialized BFGS has the printed excess and strict separation.
Article: main_krylov, s3:cor:qn, genuine named correction-free strict separation.
Proof: Apply the universal genuine correction-free excess bound and its strict positive-newest-budget consequence to the actual primitive smooth implementation. -/
theorem bfgs_excess (c : ℝ) (hc : 0<c)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2)≤
      worstTransverse (smoothBFGSClass (E := EuclideanSpace ℝ (Fin n)) c hc).policy base g N ω ∧
    (0<ω ⟨N-2,by omega⟩ → selectionValue base g N ω<worstTransverse (smoothBFGSClass (E := EuclideanSpace ℝ (Fin n)) c hc).policy base g N ω) :=
  ⟨correctionFree_excess_lower (smoothBFGSClass (E := EuclideanSpace ℝ (Fin n)) c hc) (smoothLBFGSClass_correctionFree fullMemory (fun _ hk => hk) c hc) base hb g N hN hcount ω,
    correctionFree_strict_excess (smoothBFGSClass (E := EuclideanSpace ℝ (Fin n)) c hc) (smoothLBFGSClass_correctionFree fullMemory (fun _ hk => hk) c hc) base hb g N hN hcount ω⟩

end
end krylov.Envelope
