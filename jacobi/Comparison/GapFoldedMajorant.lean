import jacobi.Comparison.GapFactorLimit
import jacobi.Finite.TwoEdgeLogRows

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
Every actual finite gap logarithm is dominated by the same summable
row after folding either spectral edge. Unlike a mere bound on the
whole product, this pointwise majorant justifies the full original
finite-product limit by dominated convergence on both half-rows.
Use: gapProduct_log_tendsto applies dominated convergence to the complete growing half-rows, rather than interchanging a formal infinite product and a limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Finite jacobi.Reference jacobi.Jacobi
open scoped Topology

/-- The folded original gap-row majorant is genuinely summable for each fixed original edge index.
Use: gapProduct_log_tendsto applies dominated convergence to the complete growing half-rows, rather than interchanging a formal infinite product and a limit.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the exceptional folded diagonal is supported at a single index. Away from it the row is the sum of the ordinary inverse-square series and the already proved translated inverse-square series. Their positive sum dominates the exceptional value too. -/
theorem foldedRowMajorant_summable (k:ℕ) : Summable (foldedRowMajorant k) := by
  -- The summability statement includes the opposite-edge index having the same folded distance.
  have hδ : Summable (fun j:ℕ => if j=k then (1:ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s:={k})
    intro j hj
    simp only [mem_singleton] at hj
    exact ite_eq_right hj
  have hp : Summable (fun j:ℕ => 2/(j+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left 2
  apply ((hδ.add hp).add ((distanceMajorant_summable k).mul_left 3)).of_nonneg_of_le (foldedRowMajorant_nonneg k)
  intro j
  by_cases hj:j=k
  · simp only [foldedRowMajorant,ite_eq_left hj]
    have h : 0≤2/(j+1:ℝ)^2+3*distanceMajorant k j := by unfold distanceMajorant; positivity
    linarith
  · simp only [foldedRowMajorant,ite_eq_right hj,zero_add]
    exact le_rfl

/-- Each actual original finite gap logarithm is bounded by one common folded summable majorant, uniformly over every genuine pair of spectral indices.
Use: gapProduct_log_tendsto dominates both true finite spectral half-rows at each fixed edge index; the opposite half has pointwise zero limit and hence no extra limiting normalization.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the inverse-square term of the already proved exact node-gap logarithm estimate is controlled by twoEdge_error_summand. In the bulk term, the pair weight dominates the two edge distances and the actual integer gap is at least one. Thus that term is at most 1/F^2, which is at most 4/d_l^2 because the original dimension is at most twice its genuine frequency. The diagonal logarithm is zero. -/
theorem gapFactorAt_log_folded_majorant {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀k j:Fin (n+1),
      |log (gapFactorAt a b ha hb n k.val j.val)|≤
        C*(foldedRowMajorant (edgeIndex (n+1) k.val-1) (edgeIndex (n+1) j.val-1)/
          (edgeIndex (n+1) k.val:ℝ)^2+4/(edgeIndex (n+1) j.val:ℝ)^2) := by
  -- Folding gives the same summable bound at either original spectral endpoint.
  obtain ⟨C,hC,hbound⟩ := comparisonGap_log_majorant ha hb
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,(tendsto_add_atTop_nat 1).eventually (frequency_degree_comparison a b)] with n hn hf
  intro k j
  by_cases h:j=k
  · subst j
    simp only [gapFactorAt,ite_true,log_one,abs_zero]
    exact mul_nonneg hC.le (add_nonneg (div_nonneg (foldedRowMajorant_nonneg _ _) (sq_nonneg _)) (by positivity))
  have hne : j.val≠k.val := fun he => h (Fin.ext he)
  rw [gapFactorAt,ite_eq_right hne,cosAngleAt_node a b ha hb k.isLt,cosAngleAt_node a b ha hb j.isLt]
  let F := frequency a b (n+1)
  let dk : ℝ := edgeIndex (n+1) k.val
  let dj : ℝ := edgeIndex (n+1) j.val
  let d : ℝ := |(k.val:ℝ)-j.val|
  let m : ℝ := pairIndex (n+1) k.val j.val
  have hdk : 0<dk := by dsimp [dk,edgeIndex]; exact_mod_cast (show 0<min (k.val+1) (n+1-k.val) by omega)
  have hdj : 0<dj := by dsimp [dj,edgeIndex]; exact_mod_cast (show 0<min (j.val+1) (n+1-j.val) by omega)
  have hd : 1≤d := Nat.pairwise_one_le_dist (fun he => hne he.symm)
  have hm : dk+dj≤m := by dsimp [dk,dj,m]; exact_mod_cast pairIndex_ge_edges k.isLt j.isLt
  have hm0 : 0<m := by linarith
  have hF : 0<F := hf.1
  have hdjN : dj≤(n:ℝ)+1 := by
    dsimp [dj]
    exact_mod_cast (show edgeIndex (n+1) j.val≤n+1 by dsimp [edgeIndex]; omega)
  have hNF : (n:ℝ)+1≤2*F := by simpa only [Nat.cast_add,Nat.cast_one] using hf.2.1
  have hpair : dk+dj≤d*m := by nlinarith [mul_le_mul_of_nonneg_right hd hm0.le]
  have hbulk : (dk+dj)/(F^2*d*m)≤4/dj^2 := by
    have h₁ : (dk+dj)/(F^2*d*m)≤1/F^2 := by
      apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hF)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hpair (sq_nonneg F)]
    apply h₁.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hF) (sq_pos_of_pos hdj)).mpr
    nlinarith
  exact (hn k j (Ne.symm h)).trans (mul_le_mul_of_nonneg_left
    (add_le_add (twoEdge_error_summand k j (Ne.symm h)) hbulk) hC.le)

end
end jacobi.Comparison
