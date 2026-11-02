import jacobi.Comparison.GapFoldedMajorant

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The two actual finite spectral half-rows have the full norming-logarithm
limit and zero limit respectively. Both use the same genuine summable
folded majorant, including the possible opposite-edge folded diagonal.
This proves the finite-product tail passage rather than assuming it.
Use: rightGapLog_tsum_tendsto retains every original right-half factor while taking the genuine finite-to-infinite norming-product limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Finite jacobi.Reference jacobi.Jacobi
open scoped Topology

/-- The complete original right spectral half-row of gap logarithms, extended by zero.
Use: rightGapLog_tsum_tendsto retains every original right-half factor while taking the genuine finite-to-infinite norming-product limit.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def rightGapLog (a b:ℝ) (ha:-1<a) (hb:-1<b) (k n j:ℕ) : ℝ :=
  if 2*j≤n then log (gapFactorAt a b ha hb n k j) else 0

/-- The complete opposite spectral half-row, indexed from its own original endpoint and extended by zero.
Use: leftGapLog_tsum_tendsto proves that the whole reflected half contributes no limiting multiplicative factor to rho_alpha.
Article: jacobi, Appendix C.4 (target/support weight ratios).
The strict half-inequality assigns a possible middle node only to rightGapLog. -/
def leftGapLog (a b:ℝ) (ha:-1<a) (hb:-1<b) (k n j:ℕ) : ℝ :=
  if 2*j<n then log (gapFactorAt a b ha hb n k (n-j)) else 0

/-- Both complete genuine finite gap half-rows have the same summable majorant at every fixed original right-edge index.
Use: rightGapLog_tsum_tendsto and leftGapLog_tsum_tendsto justify the full source product limit by actual dominated convergence on the original two spectral halves.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: at large dimension the fixed row index has its right edge distance k+1. On the right half the column distance is j+1; on the reflected left half it is also j+1. The independently proved pointwise folded majorant therefore applies to both, and the actual row plus inverse-square sequence is summable. Outside each genuine half-row the extension is zero. -/
theorem gapHalfRows_majorant {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    ∃g:ℕ→ℝ,Summable g ∧ (∀j,0≤g j) ∧ ∀ᶠn:ℕ in atTop,∀j:ℕ,
      ‖rightGapLog a b ha hb k n j‖≤g j ∧ ‖leftGapLog a b ha hb k n j‖≤g j := by
  -- The same original folded edge geometry controls both halves before the infinite sum is taken.
  obtain ⟨C,hC,hbound⟩ := gapFactorAt_log_folded_majorant ha hb
  let g (j:ℕ) : ℝ := C*(foldedRowMajorant k j/(k+1:ℝ)^2+4/(j+1:ℝ)^2)
  have hs : Summable g := by
    apply Summable.mul_left
    apply Summable.add ((foldedRowMajorant_summable k).div_const _)
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left 4
  have hg (j:ℕ) : 0≤g j := mul_nonneg hC.le (add_nonneg
    (div_nonneg (foldedRowMajorant_nonneg k j) (sq_nonneg _)) (by positivity))
  refine ⟨g,hs,hg,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (2*k)] with n hn hnk
  have hk : k<n+1 := by omega
  have hdk : edgeIndex (n+1) k=k+1 := by dsimp [edgeIndex]; omega
  intro j
  constructor
  · by_cases hj : 2*j≤n
    · have hjN : j<n+1 := by omega
      have hdj : edgeIndex (n+1) j=j+1 := by dsimp [edgeIndex]; omega
      have h := hn ⟨k,hk⟩ ⟨j,hjN⟩
      simpa only [rightGapLog,ite_eq_left hj,Real.norm_eq_abs,hdk,hdj,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,g] using h
    · simpa only [rightGapLog,ite_eq_right hj,norm_zero] using hg j
  · by_cases hj : 2*j<n
    · have hjN : n-j<n+1 := by omega
      have hdj : edgeIndex (n+1) (n-j)=j+1 := by dsimp [edgeIndex]; omega
      have h := hn ⟨k,hk⟩ ⟨n-j,hjN⟩
      simpa only [leftGapLog,ite_eq_left hj,Real.norm_eq_abs,hdk,hdj,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,g] using h
    · simpa only [leftGapLog,ite_eq_right hj,norm_zero] using hg j

/-- The entire original right half-row logarithm sum tends to the genuine infinite norming-factor logarithm series.
Use: gapProduct_log_tendsto obtains the original rho_alpha after combining this complete row with the vanishing opposite row.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: each actual finite factor has the independently proved positive norming-factor limit, so its logarithm converges. Each fixed index eventually belongs to the right half. The actual complete half-row is dominated by the proved summable folded majorant, allowing the community dominated series limit theorem. -/
theorem rightGapLog_tsum_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => ∑'j,rightGapLog a b ha hb k n j) atTop
      (𝓝 (∑'j,log (normingFactor a ha k j))) := by
  -- Positivity of every limiting factor supplies the genuine branch of the real logarithm.
  obtain ⟨g,hs,hg,hbound⟩ := gapHalfRows_majorant ha hb k
  apply tendsto_tsum_of_dominated_convergence hs _ (hbound.mono (fun n hn j => (hn j).1))
  intro j
  have ht := ((continuousAt_log (normingFactor_pos ha k j).ne').tendsto.comp (gapFactorAt_tendsto ha hb k j))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2*j)] with n hn
  exact (ite_eq_left hn).symm

/-- The entire original opposite spectral half-row logarithm sum tends to zero.
Use: gapProduct_log_tendsto shows that the full original product has precisely rho_alpha as its limit, without an unexplained opposite-edge normalization.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: each fixed reflected factor tends to one by exact original node reflection, so its logarithm tends to zero. Its index eventually belongs to the strict reflected half. The same summable original folded majorant dominates the whole growing reflected half-row, hence dominated convergence makes its full sum vanish. -/
theorem leftGapLog_tsum_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => ∑'j,leftGapLog a b ha hb k n j) atTop (𝓝 0) := by
  -- The complete growing opposite half, rather than each isolated factor alone, has vanishing total logarithm.
  obtain ⟨g,hs,hg,hbound⟩ := gapHalfRows_majorant ha hb k
  have hp (j:ℕ) : Tendsto (fun n:ℕ => leftGapLog a b ha hb k n j) atTop (𝓝 (0:ℝ)) := by
    have ht := (continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp (gapFactorAt_reflected_tendsto ha hb k j)
    simp only [log_one] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (2*j)] with n hn
    exact (ite_eq_left hn).symm
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs hp
    (hbound.mono (fun n hn j => (hn j).2))

end
end jacobi.Comparison
