import krylov.Envelope.FinalizedSelection

set_option autoImplicit false
/-!
Article: main_krylov, s3:cor:qn, genuine named-method final minimax attainers.
Use: specialize the actual final-correction minimax construction to real
HS, HZ, BFGS/L-BFGS and every positive newest-pair FC window.
Source: proved genuine named primitive smooth correction-free source
classes and actual globally consistent single-query final minimax wrappers.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Every actual correction-free smooth source method has a genuine final one-correction minimax attainer.
Use: Every actual correction-free smooth source method has a genuine final one-correction minimax attainer.
Article: main_krylov, s3:cor:qn, genuine named-method final minimax attainers.
Proof: Apply the genuine generic final-wrapper source-class and attained selection theorem to the actual named correction-free primitive smooth implementation. -/
theorem named_final_correction_attains (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hm : CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    OneCorrectionMethod (finalizedSmoothClass M N).policy ∧
      worstTransverse (finalizedSmoothClass M N).policy base g N ω=selectionValue base g N ω :=
  ⟨finalized_correctionFree_oneCorrection M hm N,
    finalized_worstTransverse_eq_selectionValue M base hb g N hN hcount ω⟩

/-- Actual Hestenes-Stiefel followed by one genuine final latest-information correction attains the true minimax value.
Use: Actual Hestenes-Stiefel followed by one genuine final latest-information correction attains the true minimax value.
Article: main_krylov, s3:cor:qn, genuine named-method final minimax attainers.
Proof: Apply the genuine generic final-wrapper source-class and attained selection theorem to the actual named correction-free primitive smooth implementation. -/
theorem hs_final_correction_attains
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    OneCorrectionMethod (finalizedSmoothClass (smoothHSClass (E := EuclideanSpace ℝ (Fin n))) N).policy ∧
      worstTransverse (finalizedSmoothClass (smoothHSClass (E := EuclideanSpace ℝ (Fin n))) N).policy base g N ω=selectionValue base g N ω :=
  named_final_correction_attains smoothHSClass smoothHSClass_correctionFree base hb g N hN hcount ω

/-- Actual Hager-Zhang followed by one genuine final latest-information correction attains the true minimax value.
Use: Actual Hager-Zhang followed by one genuine final latest-information correction attains the true minimax value.
Article: main_krylov, s3:cor:qn, genuine named-method final minimax attainers.
Proof: Apply the genuine generic final-wrapper source-class and attained selection theorem to the actual named correction-free primitive smooth implementation. -/
theorem hz_final_correction_attains
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    OneCorrectionMethod (finalizedSmoothClass (smoothHZClass (E := EuclideanSpace ℝ (Fin n))) N).policy ∧
      worstTransverse (finalizedSmoothClass (smoothHZClass (E := EuclideanSpace ℝ (Fin n))) N).policy base g N ω=selectionValue base g N ω :=
  named_final_correction_attains smoothHZClass smoothHZClass_correctionFree base hb g N hN hcount ω

/-- Every genuine positive-scalar-initialized positive newest-pair L-BFGS implementation followed by one actual final correction attains the true minimax value.
Use: Every genuine positive-scalar-initialized positive newest-pair L-BFGS implementation followed by one actual final correction attains the true minimax value.
Article: main_krylov, s3:cor:qn, genuine named-method final minimax attainers.
Proof: Apply the genuine generic final-wrapper source-class and attained selection theorem to the actual named correction-free primitive smooth implementation. -/
theorem lbfgs_final_correction_attains (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) (c : ℝ) (hc : 0<c)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    OneCorrectionMethod (finalizedSmoothClass (smoothLBFGSClass (E := EuclideanSpace ℝ (Fin n)) memory hm c hc) N).policy ∧
      worstTransverse (finalizedSmoothClass (smoothLBFGSClass (E := EuclideanSpace ℝ (Fin n)) memory hm c hc) N).policy base g N ω=selectionValue base g N ω :=
  named_final_correction_attains _ (smoothLBFGSClass_correctionFree memory hm c hc) base hb g N hN hcount ω

/-- Every genuine positive newest-pair FC window followed by one actual final correction attains the true minimax value.
Use: Every genuine positive newest-pair FC window followed by one actual final correction attains the true minimax value.
Article: main_krylov, s3:cor:qn, genuine named-method final minimax attainers.
Proof: Apply the genuine generic final-wrapper source-class and attained selection theorem to the actual named correction-free primitive smooth implementation. -/
theorem fc_final_correction_attains (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    OneCorrectionMethod (finalizedSmoothClass (smoothFCClass (E := EuclideanSpace ℝ (Fin n)) memory hm) N).policy ∧
      worstTransverse (finalizedSmoothClass (smoothFCClass (E := EuclideanSpace ℝ (Fin n)) memory hm) N).policy base g N ω=selectionValue base g N ω :=
  named_final_correction_attains _ (smoothFCClass_correctionFree memory hm) base hb g N hN hcount ω

/-- Actual positive-scalar-initialized BFGS followed by one genuine final correction attains the true minimax value.
Use: Actual positive-scalar-initialized BFGS followed by one genuine final correction attains the true minimax value.
Article: main_krylov, s3:cor:qn, genuine named-method final minimax attainers.
Proof: Apply the genuine generic final-wrapper source-class and attained selection theorem to the actual named correction-free primitive smooth implementation. -/
theorem bfgs_final_correction_attains (c : ℝ) (hc : 0<c)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    OneCorrectionMethod (finalizedSmoothClass (smoothBFGSClass (E := EuclideanSpace ℝ (Fin n)) c hc) N).policy ∧
      worstTransverse (finalizedSmoothClass (smoothBFGSClass c hc) N).policy base g N ω=selectionValue base g N ω :=
  lbfgs_final_correction_attains fullMemory (fun _ hk => hk) c hc base hb g N hN hcount ω

end
end krylov.Envelope
