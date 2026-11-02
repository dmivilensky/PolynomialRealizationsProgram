import jacobi.Finite.TwoEdgeIndices
import jacobi.Reference.IndexMajorant

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The complete inverse-square part of each original two-edge logarithm
row has a uniform inverse-square bound in the nearer-edge index.
The earlier continuum quadratic-gap majorant is reused after folding;
the equal-distance opposite-edge pair is included explicitly.
Use: twoEdge_error_row controls the full finite relative-gap logarithm, including the opposite-edge node with the same nearer-edge distance.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset jacobi.Jacobi jacobi.Reference

/-- The folded row majorant with its genuine equal-distance term included.
Use: twoEdge_error_row controls the full finite relative-gap logarithm, including the opposite-edge node with the same nearer-edge distance.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def foldedRowMajorant (k l:ℕ) : ℝ :=
  if l=k then 1 else 2/(l+1:ℝ)^2+3*distanceMajorant k l

/-- The actual folded row majorant is nonnegative at every pair of positive spectral distances.
Use: the full two-edge folding bound may enlarge every original erased index set to the complete finite spectrum.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: its equal-distance value is one; every other term is a nonnegative reciprocal square. -/
theorem foldedRowMajorant_nonneg (k l:ℕ) : 0≤foldedRowMajorant k l := by
  unfold foldedRowMajorant distanceMajorant
  split_ifs <;> positivity

/-- Every prefix of the folded row majorant has one bound independent of its center and length.
Use: twoEdge_error_row sums the original finite logarithm perturbations uniformly over the whole growing spectrum.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the equal-distance term contributes at most one. The ordinary inverse-square prefix is bounded by its convergent infinite series, and the genuine translated inverse-square prefix is bounded by twice that same series using the already proved continuum row estimate. -/
theorem foldedRowMajorant_prefix (k N:ℕ) :
    (∑j∈range N,foldedRowMajorant k j)≤1+8*(∑'j:ℕ,1/(j+1:ℝ)^2) := by
  -- The same p-series constant controls every original folded center.
  have hs : Summable (fun j:ℕ => 1/(j+1:ℝ)^2) := by
    simpa only [one_pow] using jacobi.Bessel.inverse_square_majorant_summable 1
  have h₁ := hs.sum_le_tsum (range N) (fun _ _ => by positivity)
  have h₂ := ((distanceMajorant_summable k).sum_le_tsum (range N)
    (fun _ _ => by unfold distanceMajorant; positivity)).trans (distanceMajorant_tsum_le k)
  have hzero : (∑j∈range N,if j=k then (1:ℝ) else 0)≤1 := by
    rw [sum_ite_eq']
    split_ifs <;> norm_num
  have hpoint (j:ℕ) : foldedRowMajorant k j≤
      (if j=k then (1:ℝ) else 0)+2/(j+1:ℝ)^2+3*distanceMajorant k j := by
    by_cases hj:j=k
    · rw [foldedRowMajorant,ite_eq_left hj,ite_eq_left hj]
      have hnonneg : 0≤2/(j+1:ℝ)^2+3*distanceMajorant k j := by unfold distanceMajorant; positivity
      linarith
    · simp only [foldedRowMajorant,ite_eq_right hj,zero_add]
      exact le_rfl
  have h := sum_le_sum (fun j (_hj:j∈range N) => hpoint j)
  have he : (∑j∈range N,((if j=k then (1:ℝ) else 0)+2/(j+1:ℝ)^2+3*distanceMajorant k j))=
      (∑j∈range N,if j=k then (1:ℝ) else 0)+2*(∑j∈range N,1/(j+1:ℝ)^2)+3*∑j∈range N,distanceMajorant k j := by
    simp only [sum_add_distrib,div_eq_mul_inv,one_mul,← mul_sum]
  rw [he] at h
  linarith

/-- Each genuine off-diagonal two-edge error summand is bounded by the previously proved continuum quadratic-gap majorant at its folded indices.
Use: twoEdge_error_row sums these actual pointwise estimates to obtain the complete finite inverse-square logarithm bound.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the original pair weight dominates the sum of the two nearer-edge distances, and index distance dominates their difference. For unequal folded distances use the already proved quadratic-gap majorant. For equal folded distances the genuine original nodes remain distinct integers, so their index gap is at least one and the pair weight at least two. -/
theorem twoEdge_error_summand {N:ℕ} (i j:Fin N) (hij:i≠j) :
    (1/(edgeIndex N i.val:ℝ)^2+1/(edgeIndex N j.val:ℝ)^2)/
      (|(i.val:ℝ)-j.val| *(pairIndex N i.val j.val:ℝ))≤
      foldedRowMajorant (edgeIndex N i.val-1) (edgeIndex N j.val-1)/(edgeIndex N i.val:ℝ)^2 := by
  -- The folded diagonal is a genuine opposite-edge pair and is treated before applying the off-diagonal continuum bound.
  let di := edgeIndex N i.val
  let dj := edgeIndex N j.val
  have hdi : 0<di := by dsimp [di,edgeIndex]; omega
  have hdj : 0<dj := by dsimp [dj,edgeIndex]; omega
  have hdiR : (1:ℝ)≤di := by exact_mod_cast hdi
  have hdjR : (1:ℝ)≤dj := by exact_mod_cast hdj
  have hm : (di:ℝ)+dj≤(pairIndex N i.val j.val:ℝ) := by exact_mod_cast pairIndex_ge_edges i.isLt j.isLt
  have hd : (1:ℝ)≤|(i.val:ℝ)-j.val| := by
    have hne : i.val≠j.val := fun he => hij (Fin.ext he)
    exact Nat.pairwise_one_le_dist hne
  have hdist := edgeIndex_distance i.isLt j.isLt
  have hcdi : ((di-1:ℕ):ℝ)+1=(di:ℝ) := by exact_mod_cast Nat.sub_add_cancel hdi
  have hcdj : ((dj-1:ℕ):ℝ)+1=(dj:ℝ) := by exact_mod_cast Nat.sub_add_cancel hdj
  by_cases he:di=dj
  · have he' : dj-1=di-1 := by omega
    have hden : (2:ℝ)≤|(i.val:ℝ)-j.val| *(pairIndex N i.val j.val:ℝ) := by
      have hp : (2:ℝ)≤(pairIndex N i.val j.val:ℝ) := by rw [← he] at hm; linarith
      have hh := mul_le_mul_of_nonneg_right hd (show 0≤(pairIndex N i.val j.val:ℝ) by positivity)
      linarith
    change _≤foldedRowMajorant (di-1) (dj-1)/(di:ℝ)^2
    rw [foldedRowMajorant,ite_eq_left he']
    change (1/(di:ℝ)^2+1/(dj:ℝ)^2)/_≤_
    rw [← he]
    calc
      _ ≤ (1/(di:ℝ)^2+1/(di:ℝ)^2)/2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = _ := by ring
  · have hneq : di-1≠dj-1 := by omega
    have hdelt : 0< (|(dj:ℝ)^2-(di:ℝ)^2|) := by
      apply abs_pos.mpr
      intro hz
      have hcast : (di:ℝ)≠dj := by exact_mod_cast he
      apply hcast
      nlinarith
    have hprod : |(dj:ℝ)^2-(di:ℝ)^2|≤|(i.val:ℝ)-j.val| *(pairIndex N i.val j.val:ℝ) := by
      calc
        _ = |(di:ℝ)-dj| *((di:ℝ)+dj) := by
          rw [show (dj:ℝ)^2-(di:ℝ)^2= -(((di:ℝ)-dj)*((di:ℝ)+dj)) by ring,
            abs_neg,abs_mul,abs_of_pos (by linarith : (0:ℝ)<(di:ℝ)+dj)]
        _ ≤ _ := mul_le_mul hdist hm (by positivity) (by positivity)
    have hbound := inverse_square_gap_majorant hneq
    rw [hcdi,hcdj] at hbound
    have hfold : foldedRowMajorant (di-1) (dj-1)=2/(dj:ℝ)^2+3*distanceMajorant (di-1) (dj-1) := by
      rw [foldedRowMajorant,ite_eq_right hneq.symm,hcdj]
    change _≤foldedRowMajorant (di-1) (dj-1)/(di:ℝ)^2
    rw [hfold]
    exact (div_le_div_of_nonneg_left (by positivity) hdelt hprod).trans hbound

/-- The complete original finite inverse-square perturbation row has one uniform inverse-square edge bound.
Use: comparisonWeight_log_bound sums the first part of the actual finite logarithmic factor estimate; the remaining harmonic part is controlled separately.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: apply the actual folded pointwise bound, enlarge the erased row to the whole nonnegative finite spectrum and fold it with multiplicity at most two. The independently proved continuum p-series prefix bound then gives one constant for every dimension and spectral index. -/
theorem twoEdge_error_row {N:ℕ} (i:Fin N) :
    (∑j∈univ.erase i,(1/(edgeIndex N i.val:ℝ)^2+1/(edgeIndex N j.val:ℝ)^2)/
      (|(i.val:ℝ)-j.val| *(pairIndex N i.val j.val:ℝ)))≤
      (2*(1+8*(∑'j:ℕ,1/(j+1:ℝ)^2)))/(edgeIndex N i.val:ℝ)^2 := by
  -- No infinite approximation of the original finite row is assumed; only its proved nonnegative majorant is enlarged.
  let f := foldedRowMajorant (edgeIndex N i.val-1)
  have hsum : (∑j:Fin N,f (edgeIndex N j.val-1))≤2*(1+8*(∑'j:ℕ,1/(j+1:ℝ)^2)) := by
    calc
      _ = ∑j∈range N,f (edgeIndex N j-1) := Fin.sum_univ_eq_sum_range _ _
      _ ≤ 2*∑j∈range N,f j := edgeIndex_sum_le f (foldedRowMajorant_nonneg _) N
      _ ≤ _ := mul_le_mul_of_nonneg_left (foldedRowMajorant_prefix _ N) (by norm_num)
  calc
    _ ≤ ∑j∈univ.erase i,f (edgeIndex N j.val-1)/(edgeIndex N i.val:ℝ)^2 :=
      sum_le_sum (fun j hj => twoEdge_error_summand i j (mem_erase.mp hj).1.symm)
    _ ≤ ∑j:Fin N,f (edgeIndex N j.val-1)/(edgeIndex N i.val:ℝ)^2 :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by
        exact div_nonneg (foldedRowMajorant_nonneg _ _) (sq_nonneg _))
    _ = (∑j:Fin N,f (edgeIndex N j.val-1))/(edgeIndex N i.val:ℝ)^2 := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hsum (sq_nonneg _)

end
end jacobi.Finite
