import krylov.Envelope.CorrectionFreeExcessWitness

set_option autoImplicit false
/-!
Article: Corollary B.19 [s3:thm:cf] of krylov.tex.
Use: obtain the printed universal excess lower bound and strict failure to attain the true selection value when the newest budget is positive.
Source: the actual feasible excess witness, genuine compact worst-variation attainment and positivity of true active CG energy.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual worst transverse variation of every genuine correction-free smooth method is bounded below by the printed square-root excess.
Use: The actual worst transverse variation of every genuine correction-free smooth method is bounded below by the printed square-root excess.
Article: main_krylov, s3:thm:cf, the genuine price without a final correction.
Proof: Use the genuine feasible excess scenario in the actual attained maximum. -/
theorem correctionFree_excess_lower (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2)≤
      worstTransverse M.policy base g N ω := by
  obtain ⟨k,rfl⟩ : ∃ k,N=k+2 := ⟨N-2,by omega⟩
  obtain ⟨Θ,hΘ,hν⟩ := correctionFree_excess_witness M hfree base hb g k hcount ω
  have hmax := (worstTransverse_attained M.policy base g (k+2) ω).2 ⟨Θ,hΘ,hν⟩
  simpa only [show k+2-2=k by omega,show k+2-1=k+1 by omega] using hmax

/-- Every actual correction-free smooth method has strictly larger worst variation than the selection value when its final increment budget is positive.
Use: Every actual correction-free smooth method has strictly larger worst variation than the selection value when its final increment budget is positive.
Article: main_krylov, s3:thm:cf, the genuine price without a final correction.
Proof: The genuine last active energy is positive, so the square-root excess is strictly larger than the nonnegative selection value. -/
theorem correctionFree_strict_excess (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0)
    (hw : 0<ω ⟨N-2,by omega⟩) :
    selectionValue base g N ω<worstTransverse M.policy base g N ω := by
  -- Actual activity makes the newest squared-response contribution strictly positive.
  have hc := cgEnergy_pos base hb g (N-1) (by omega)
  have hω : 0<(ω ⟨N-2,by omega⟩ : ℝ) := hw
  have hp : 0<cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2 :=
    mul_pos hc (sq_pos_of_pos hω)
  have hv := selectionValue_nonneg base g N ω
  have hs : selectionValue base g N ω<
      Real.sqrt ((selectionValue base g N ω)^2+cgEnergy base g (N-1)*(ω ⟨N-2,by omega⟩ : ℝ)^2) := by
    apply (Real.lt_sqrt hv).2
    linarith
  exact hs.trans_le (correctionFree_excess_lower M hfree base hb g N hN hcount ω)
end
end krylov.Envelope
