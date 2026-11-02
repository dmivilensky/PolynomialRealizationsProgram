import jacobi.Comparison.GramSummands

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Use: gramPerturbation_entry_bound sums the proved genuine original spectral perturbation majorant over every actual node of the growing finite matrix.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Jacobi jacobi.Finite
open scoped Topology

/-- The complete original inverse-square edge-distance row has a dimension-independent summable bound.
Use: gramPerturbation_entry_bound sums the proved genuine original spectral perturbation majorant over every actual node of the growing finite matrix.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Source: the classical inverse-square p-series and the finite edge fold, proved here using the existing two-edge index identity.
Proof: each original folded distance occurs at most twice. The resulting positive inverse-square prefix is bounded by its genuinely convergent infinite series. The original edge index is positive, so subtracting and restoring one does not alter any summand. -/
theorem edge_inverse_square_sum (N:ℕ) :
    (∑k:Fin N,1/(edgeIndex N k.val:ℝ)^2)≤2*(∑'j:ℕ,1/(j+1:ℝ)^2) := by
  -- Both original endpoint rows share the same positive-index p-series.
  let f (j:ℕ) : ℝ := 1/(j+1:ℝ)^2
  have hs : Summable f := by simpa only [f,one_pow] using jacobi.Bessel.inverse_square_majorant_summable 1
  have he : (∑k:Fin N,1/(edgeIndex N k.val:ℝ)^2)=∑j∈range N,f (edgeIndex N j-1) := by
    calc
      _ = ∑k:Fin N,f (edgeIndex N k.val-1) := by
        apply sum_congr rfl
        intro k _
        have hpos : 0<edgeIndex N k.val := by dsimp [edgeIndex]; omega
        have hc : ((edgeIndex N k.val-1:ℕ):ℝ)+1=(edgeIndex N k.val:ℝ) := by exact_mod_cast Nat.sub_add_cancel hpos
        dsimp [f]
        rw [hc]
      _ = _ := Fin.sum_univ_eq_sum_range (fun j => f (edgeIndex N j-1)) N
  rw [he]
  exact (edgeIndex_sum_le f (fun _ => by dsimp [f]; positivity) N).trans
    (mul_le_mul_of_nonneg_left (hs.sum_le_tsum (range N) (fun _ _ => by dsimp [f]; positivity)) (by norm_num))

/-- The actual original target Gram perturbation has a uniform O(1/N) entry bound on the entire physical half-chain.
Use: the quantitative original Schur normalization and Cholesky coefficient estimates start with this same actual finite Gram bound, before proving the additional growing-section coercivity and continuum kernel limits.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: use the exact original spectral summand representation and the proved uniform summand estimate. Its inverse-square edge row has bounded total mass over all original nodes. The common remainder contributes N*epsilon_N, eventually at most one by its proved zero limit. Combine both constants to obtain one bound for all original half-chain degree pairs. -/
theorem gramPerturbation_entry_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i j:Fin (n+1),2*i.val≤n+1→2*j.val≤n+1→
      ((n:ℝ)+1)*|gramPerturbation a b ha hb n i j|≤C := by
  -- Sum the full original spectral row; the common error is multiplied by the actual matrix size only once.
  obtain ⟨C,hC,ε,hε,hlim,hbound⟩ := gramSummand_bound ha hb
  let Z : ℝ := ∑'j:ℕ,1/(j+1:ℝ)^2
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  refine ⟨2*C*Z+1,by positivity,?_⟩
  filter_upwards [hbound,hlim.eventually (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn hsmall
  intro i j hi hj
  rw [gramPerturbation_sum]
  calc
    _ ≤ ((n:ℝ)+1)*∑k:Fin (n+1),|gramSummand a b ha hb n i j k| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑k:Fin (n+1),((n:ℝ)+1)*|gramSummand a b ha hb n i j k| := mul_sum _ _ _
    _ ≤ ∑k:Fin (n+1),(C/(edgeIndex (n+1) k.val:ℝ)^2+ε n) := sum_le_sum (fun k _ => hn i j hi hj k)
    _ = C*(∑k:Fin (n+1),1/(edgeIndex (n+1) k.val:ℝ)^2)+((n:ℝ)+1)*ε n := by
      rw [sum_add_distrib]
      simp only [div_eq_mul_inv,one_mul,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    _ ≤ C*(2*Z)+1 := add_le_add (mul_le_mul_of_nonneg_left (edge_inverse_square_sum (n+1)) hC.le) hsmall.le
    _ = _ := by ring

end
end jacobi.Comparison
