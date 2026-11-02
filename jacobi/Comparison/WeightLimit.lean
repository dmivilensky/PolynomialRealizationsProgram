import jacobi.Comparison.GapHalfRows
import jacobi.Comparison.WeightError
import jacobi.Finite.HalfRows

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The genuine finite relative gap products and normalized target/support
probability ratios have the actual original right-edge limit rho_alpha.
The two complete growing spectral half-rows are controlled by proved
summable majorants; the original normalizer has its independently
proved limit one. No finite-product tail limit is assumed.
Use: relativeGapProductAt_tendsto states the full source finite-product limit as a standard sequence; every eventual valid index has exactly its original finite product.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Support jacobi.Reference jacobi.Finite
open scoped Topology

/-- The original finite relative gap product on an ordinary index space, extended by one beyond its genuine dimension.
Use: relativeGapProductAt_tendsto states the full source finite-product limit as a standard sequence; every eventual valid index has exactly its original finite product.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def relativeGapProductAt (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) : ℝ :=
  if hk:k<n+1 then relativeGapProduct a b ha hb n ⟨k,hk⟩ else 1

/-- The exact original finite relative product has its full logarithmic norming-series limit at every fixed original right-edge index.
Use: relativeGapProductAt_tendsto exponentiates this actual limit to the genuine original rho_alpha.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the independently proved limits of the complete genuine right and reflected-left half-rows are the norming-logarithm sum and zero. Both rows are actually finitely supported at each dimension. The exact finite half-row partition identifies their sum with the logarithm of the same original relative product. -/
theorem gapProduct_log_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => log (relativeGapProductAt a b ha hb n k)) atTop
      (𝓝 (∑'j,log (normingFactor a ha k j))) := by
  -- Each complete spectral half has already passed its own dominated-convergence audit.
  have ht := (rightGapLog_tsum_tendsto ha hb k).add (leftGapLog_tsum_tendsto ha hb k)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  have hk : k<n+1 := by omega
  rw [relativeGapProductAt,dite_eq_left hk,gapFactorAt_log_sum]
  have hright : (∑'j,rightGapLog a b ha hb k n j)=∑j∈range (n+1),rightGapLog a b ha hb k n j := by
    apply tsum_eq_sum
    intro j hj
    have h : ¬2*j≤n := by have := not_lt.mp (show ¬j<n+1 by simpa only [mem_range] using hj); omega
    exact ite_eq_right h
  have hleft : (∑'j,leftGapLog a b ha hb k n j)=∑j∈range (n+1),leftGapLog a b ha hb k n j := by
    apply tsum_eq_sum
    intro j hj
    have h : ¬2*j<n := by have := not_lt.mp (show ¬j<n+1 by simpa only [mem_range] using hj); omega
    exact ite_eq_right h
  rw [hright,hleft]
  change (∑j∈range (n+1),rightGapLog a b ha hb k n j)+(∑j∈range (n+1),leftGapLog a b ha hb k n j)=
    ∑j:Fin (n+1),log (gapFactorAt a b ha hb n k j.val)
  have hsum : (∑j:Fin (n+1),log (gapFactorAt a b ha hb n k j.val))=
      ∑j∈range (n+1),log (gapFactorAt a b ha hb n k j) :=
    Fin.sum_univ_eq_sum_range (fun j => log (gapFactorAt a b ha hb n k j)) (n+1)
  rw [hsum]
  exact (sum_two_halves n (fun j => log (gapFactorAt a b ha hb n k j))).symm

/-- The entire actual original finite relative gap product tends to its genuine original infinite norming ratio at every fixed right-edge index.
Use: comparisonWeightAt_tendsto obtains the printed original target/support weight ratio rho_alpha, which fixes the amplitude of every target eigenvector edge limit.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: exponentiate the full proved genuine logarithm-sum limit. The actual positive infinite norming product equals the exponential of its convergent logarithm series; positivity of every original finite product recovers that same product from its logarithm. -/
theorem relativeGapProductAt_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => relativeGapProductAt a b ha hb n k) atTop (𝓝 (normingRatio a ha k)) := by
  -- The actual infinite product and its true positive logarithms have independently proved convergence.
  have he : exp (∑'j,log (normingFactor a ha k j))=normingRatio a ha k :=
    Real.rexp_tsum_eq_tprod (normingFactor_pos ha k) (normingFactor_log_summable ha k)
  have ht := continuous_exp.continuousAt.tendsto.comp (gapProduct_log_tendsto ha hb k)
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  have hk : k<n+1 := by omega
  change exp (log (relativeGapProductAt a b ha hb n k))=relativeGapProductAt a b ha hb n k
  simp only [relativeGapProductAt,dite_eq_left hk]
  exact exp_log (relativeGapProduct_pos a b ha hb n ⟨k,hk⟩)

/-- The literal original gap-product normalizer tends to one.
Use: comparisonWeightAt_tendsto divides the genuine finite-product limit by this same original normalizer, preserving the exact rho_alpha amplitude.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the proved stronger limit N*|S_n-1|->0 bounds |S_n-1| because the true dimension N is at least one. Squeeze that nonnegative absolute error and use the standard distance characterization of convergence. -/
theorem comparisonNormalizer_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (comparisonNormalizer a b ha hb) atTop (𝓝 1) := by
  have habs : Tendsto (fun n:ℕ => |comparisonNormalizer a b ha hb n-1|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) _ (comparisonNormalizer_error ha hb)
    intro n
    have hN : 1≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hN (abs_nonneg (comparisonNormalizer a b ha hb n-1))
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Real.dist_eq] using habs

/-- The actual target/support probability ratio on scalar indices, with irrelevant unit padding beyond the genuine original spectrum.
Use: comparisonWeightAt_tendsto supplies precisely the fixed original weight ratio required by the Gram and eigenvector limits.
Article: jacobi, Appendix C.4 (target/support weight ratios).
-/
def comparisonWeightAt (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) : ℝ :=
  if hk:k<n+1 then (targetMeasure a b ha hb n).weight ⟨k,hk⟩/(supportMeasure a b ha hb n).weight ⟨k,hk⟩ else 1

/-- Every fixed actual original target/support weight ratio tends to its genuine original norming ratio at the right spectral edge.
Use: the full target Gram limit and target eigenvector normalization use the exact original factor rho_alpha, with no separate weight-limit premise.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: divide the proved limit of the complete original relative product by the proved limit one of its actual support-weighted normalizer. At every eventual valid original index, the exact finite probability-ratio formula identifies that quotient with the actual target/support ratio. -/
theorem comparisonWeightAt_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => comparisonWeightAt a b ha hb n k) atTop (𝓝 (normingRatio a ha k)) := by
  -- The same original numerator and normalizer are used in the finite identity and both independent limits.
  have ht := (relativeGapProductAt_tendsto ha hb k).div (comparisonNormalizer_tendsto ha hb) (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  have hk : k<n+1 := by omega
  change relativeGapProductAt a b ha hb n k/comparisonNormalizer a b ha hb n=comparisonWeightAt a b ha hb n k
  simp only [comparisonWeightAt,relativeGapProductAt,dite_eq_left hk]
  exact (comparisonWeight_ratio a b ha hb n ⟨k,hk⟩).symm

end
end jacobi.Comparison
