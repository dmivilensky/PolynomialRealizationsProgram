import krylov.Stability.ObliqueResponseBounds

/-!
Article: main_krylov, thm:UCq, quantitative genuine terminal response geometry.
Use: Reuse the actual full-basis, oblique flag and measured-model algebra
in the uniform second-order RFC expansion without a smallest CG energy.
Source: proved genuine Gram conditioning, exact finite correction identities
and the existing weighted oblique response comparison.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The real finite step sequence containing only the supplied final searched line.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
-/
def terminalLineSequence (N : ℕ) (v : EuclideanSpace ℝ (Fin n)) (j : ℕ) : EuclideanSpace ℝ (Fin n) :=
  if j=N-1 then v else 0

/-- Every genuine earlier tail of the single-last-line sequence is exactly that actual line, and its final tail is zero.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: The finite conditional sum selects the original last index precisely when that index belongs to the real tail interval.
-/
theorem terminalLineSequence_tail (N l : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    (∑ j ∈ Ico (l+1) N, terminalLineSequence N v j)=if l+1<N then v else 0 := by
  have hi : l+1≤N-1 ∧ N-1<N ↔ l+1<N := by omega
  simp only [terminalLineSequence,sum_ite_eq',mem_Ico,hi]

/-- Two genuine single-last-line sequences differ only by their true line displacement difference.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: The selected last coordinate has the actual vector difference; every other real coordinate is zero.
-/
theorem terminalLineSequence_difference (N j : ℕ) (v w : EuclideanSpace ℝ (Fin n)) :
    ‖terminalLineSequence N v j-terminalLineSequence N w j‖≤‖v-w‖ := by
  by_cases hj : j=N-1
  · simp only [terminalLineSequence,ite_eq_left hj,le_refl]
  · simp only [terminalLineSequence,ite_eq_right hj,sub_self,norm_zero,norm_nonneg]

/-- The true terminal-line oblique fresh response is bounded by twice the real total increment budget times its actual line norm.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Reuse the genuine half-Gram flag bound and actual spectral operator norms in the existing oblique response sum. Every real single-last-line tail has norm at most the supplied line norm.
-/
theorem terminal_oblique_response_norm (T : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hT : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) :
    ‖obliqueResponse T E (terminalLineSequence n v)‖≤2*(∑ l ∈ range n, ‖E l‖)*‖v‖ := by
  unfold obliqueResponse
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ l ∈ range n, 2*‖E l‖*‖v‖ := by
      apply sum_le_sum
      intro l _hl
      have htail : ‖∑ j ∈ Ico (l+1) n, terminalLineSequence n v j‖≤‖v‖ := by
        rw [terminalLineSequence_tail]
        split <;> simp only [norm_zero,norm_nonneg,le_refl]
      have hflag : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag T l)ᵀ‖≤2 := by
        rw [Matrix.l2_opNorm_toEuclideanCLM,transpose_norm]
        exact transportedFlag_norm_two T hT l
      have ht := (Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag T l)ᵀ).le_opNorm
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (∑ j ∈ Ico (l+1) n, terminalLineSequence n v j))
      apply ht.trans
      have hE := (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l)).le_opNorm (∑ j ∈ Ico (l+1) n, terminalLineSequence n v j)
      rw [Matrix.l2_opNorm_toEuclideanCLM] at hE
      exact (mul_le_mul hflag (hE.trans (mul_le_mul_of_nonneg_left htail (norm_nonneg _)))
        (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    _ = _ := by rw [← sum_mul,← mul_sum]

/-- Actual terminal fresh responses have a uniform total-budget bound from the true line error and reference-line-weighted oblique flag errors.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Apply the existing finite oblique-response comparison to the genuine single-last-line sequences. Their actual earlier tails retain the reference line as a weight; the real final tail is zero.
-/
theorem terminal_oblique_response_difference (T Q : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (v w : EuclideanSpace ℝ (Fin n))
    {ε η : ℝ} (hε : 0≤ε) (hη : 0≤η) (hT : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) (hline : ‖v-w‖≤ε)
    (hflag : ∀ l<n-1, ‖w‖*‖transportedFlag T l-transportedFlag Q l‖≤η) :
    ‖obliqueResponse T E (terminalLineSequence n v)-obliqueResponse Q E (terminalLineSequence n w)‖≤
      (∑ l ∈ range n, ‖E l‖)*(2*(n : ℝ)*ε+η) := by
  apply obliqueResponse_difference_bound T Q E _ _ hε hT
    (fun j _hj => (terminalLineSequence_difference n j v w).trans hline)
  intro l _hl
  rw [terminalLineSequence_tail]
  by_cases ht : l+1<n
  · rw [ite_eq_left ht]
    exact hflag l (by omega)
  · rw [ite_eq_right ht,norm_zero,zero_mul]
    exact hη

end
end krylov.Correction
