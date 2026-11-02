import jacobi.Support.WeightedSegmentRight

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The full source assertion holds on every actual spectral interpolation
segment with one common positive constant. Exact parameter reflection
transfers both function and spectral derivative estimates to the other
half without changing the original spectral probabilities.
Use: the target/support Gram comparison applies the mean value theorem on each genuine node segment, with the printed summable spectral-tail bounds; these estimates feed the uniform Gram limit and Theorems A–B.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The complete original support-weighted interpolation estimates hold for every original node and every physical half-chain polynomial degree.
Use: the target/support Gram comparison applies the mean value theorem on each genuine node segment, with the printed summable spectral-tail bounds; these estimates feed the uniform Gram limit and Theorems A–B.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the right spectral half is already proved for each full original segment. Reverse the remaining genuine spectral index and exchange the actual endpoint parameters. Both original endpoints negate, the support probability is unchanged and the exact polynomial and derivative reflection preserves their absolute values. Increase both proved positive constants to their sum. -/
theorem supportPolynomial_segment_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i:Fin (n+1),2*i.val≤n+1→
      ∀k:Fin (n+1),∀x:ℝ,
      x∈uIcc (jacobi.Jacobi.modelNode a b (n+1) k.val) ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k)→
      sqrt (((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k)*|(supportPolynomial a b ha hb n i).eval x|≤C ∧
      sqrt (((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k)*|(supportPolynomial a b ha hb n i).derivative.eval x|≤
        C*((n:ℝ)+1)^2/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ) := by
  -- Both halves refer to the same actual corrected support chain and original target zeros.
  obtain ⟨A,hA,h₁⟩ := supportPolynomial_right_segment_bounds ha hb
  obtain ⟨B,hB,h₂⟩ := supportPolynomial_right_segment_bounds hb ha
  refine ⟨A+B,by positivity,?_⟩
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  intro i hi k x hx
  by_cases hk : 2*k.val≤n
  · have hd : jacobi.Jacobi.edgeIndex (n+1) k.val=k.val+1 := by
      dsimp [jacobi.Jacobi.edgeIndex]
      omega
    rw [hd,Nat.cast_add,Nat.cast_one]
    obtain ⟨hv,hd⟩ := hn₁ i hi k hk x hx
    exact ⟨hv.trans (le_add_of_nonneg_right hB.le),hd.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le)
        (sq_nonneg ((n:ℝ)+1))) (by positivity))⟩
  · let j := k.rev
    have hj : 2*j.val≤n := by dsimp [j,Fin.rev]; omega
    have hd : jacobi.Jacobi.edgeIndex (n+1) k.val=j.val+1 := by
      dsimp [jacobi.Jacobi.edgeIndex,j,Fin.rev]
      omega
    have hnode : (jacobi.Jacobi.nodes a b ha hb (n+1)).value k=
        -(jacobi.Jacobi.nodes b a hb ha (n+1)).value j := by
      simpa only [j,Fin.rev_rev] using jacobi.Jacobi.nodes_reflection ha hb j
    have hmodel : jacobi.Jacobi.modelNode a b (n+1) k.val=
        - jacobi.Jacobi.modelNode b a (n+1) j.val := by
      have h := jacobi.Jacobi.modelNode_reflection ha hb j.isLt
      rwa [show (n+1)-1-j.val=k.val by dsimp [j,Fin.rev]; omega] at h
    have hx' : -x∈uIcc (jacobi.Jacobi.modelNode b a (n+1) j.val)
        ((jacobi.Jacobi.nodes b a hb ha (n+1)).value j) := by
      rw [hnode,hmodel] at hx
      rcases mem_uIcc.mp hx with h | h
      · exact mem_uIcc_of_ge (by linarith [h.2]) (by linarith [h.1])
      · exact mem_uIcc_of_le (by linarith [h.2]) (by linarith [h.1])
    have hw : (supportMeasure a b ha hb n).weight k=(supportMeasure b a hb ha n).weight j := by
      simpa only [j,Fin.rev_rev] using supportMeasure_weight_reflection a b ha hb n j
    have hpar := supportPolynomial_reflected_norms a b ha hb n i (-x)
    simp only [neg_neg] at hpar
    obtain ⟨hv,hderiv⟩ := hn₂ i hi j hj (-x) hx'
    rw [← hw,← hpar.1] at hv
    rw [← hw,← hpar.2] at hderiv
    rw [hd,Nat.cast_add,Nat.cast_one]
    exact ⟨hv.trans (le_add_of_nonneg_left hA.le),hderiv.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le)
        (sq_nonneg ((n:ℝ)+1))) (by positivity))⟩

end
end jacobi.Support
