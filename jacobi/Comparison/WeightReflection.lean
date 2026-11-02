import jacobi.Comparison.WeightLimit

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
Exact original model-node, target-node and support-probability reflection
transfers the complete right-edge weight-ratio limit to the left edge.
The literal normalizer reflects too, so no normalization constant is
lost when exchanging the two original endpoint parameters.
Use: relativeGapProduct_reflection and the actual original normalizer reflection provide the left-edge counterpart of the proved right-edge weight ratio limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Support jacobi.Reference jacobi.Jacobi
open scoped Topology

/-- The actual finite gap factors reflect exactly under exchange of the two original endpoint parameters.
Use: relativeGapProduct_reflection and the actual original normalizer reflection provide the left-edge counterpart of the proved right-edge weight ratio limit.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: reflect both original target nodes and both original corrected support nodes. Each actual gap changes sign, so its absolute value is unchanged. The omitted diagonal remains the omitted diagonal under the genuine finite reversal. -/
theorem gapFactorAt_reflection (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k j:Fin (n+1)) :
    gapFactorAt a b ha hb n k.rev.val j.rev.val=gapFactorAt b a hb ha n k.val j.val := by
  -- Reflection preserves the actual complete index set, including the diagonal convention.
  by_cases h:j=k
  · subst j
    simp only [gapFactorAt,ite_true]
  have hne : j.val≠k.val := fun he => h (Fin.ext he)
  have hrne : j.rev.val≠k.rev.val := fun he => h (Fin.rev_injective (Fin.ext he))
  have hm (i:Fin (n+1)) : modelNode a b (n+1) i.rev.val= -modelNode b a (n+1) i.val := by
    have hi : (n+1)-1-i.val=i.rev.val := by rw [Fin.val_rev]; omega
    rw [← hi]
    exact modelNode_reflection (n:=n+1) (k:=i.val) ha hb i.isLt
  have hc (i:Fin (n+1)) : cos (finiteAngleAt a b ha hb (n+1) i.rev.val)=
      -cos (finiteAngleAt b a hb ha (n+1) i.val) := by
    rw [cosAngleAt_node a b ha hb i.rev.isLt,cosAngleAt_node b a hb ha i.isLt]
    exact nodes_reflection ha hb i
  simp only [gapFactorAt,ite_eq_right hne,ite_eq_right hrne]
  rw [hm k,hm j,hc k,hc j]
  simp only [neg_sub_neg,abs_sub_comm]

/-- The genuine original finite relative gap product reflects exactly under exchange of the endpoint parameters.
Use: comparisonNormalizer_reflection preserves the original weighted normalization and comparisonWeightAt_reflected_tendsto supplies the exact left-edge rho_beta limit.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: use the independently proved full scalar-gap logarithm sum for both original products. Reverse its actual finite index set and apply exact factor reflection. The original products are positive, so exponentiating the logarithm identity recovers the same actual product. -/
theorem relativeGapProduct_reflection (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    relativeGapProduct a b ha hb n k.rev=relativeGapProduct b a hb ha n k := by
  -- The full original product, rather than only its eventual asymptotic, is reflected.
  have he : log (relativeGapProduct a b ha hb n k.rev)=log (relativeGapProduct b a hb ha n k) := by
    rw [gapFactorAt_log_sum,gapFactorAt_log_sum]
    calc
      _ = ∑j:Fin (n+1),log (gapFactorAt a b ha hb n k.rev.val j.rev.val) :=
        (Equiv.sum_comp Fin.revPerm (fun j => log (gapFactorAt a b ha hb n k.rev.val j.val))).symm
      _ = _ := by apply sum_congr rfl; intro j _; rw [gapFactorAt_reflection]
  have h := congrArg exp he
  simpa only [exp_log (relativeGapProduct_pos a b ha hb n k.rev),exp_log (relativeGapProduct_pos b a hb ha n k)] using h

/-- The literal original support-weighted gap normalizer reflects exactly under parameter exchange.
Use: comparisonWeightAt_reflection obtains the left original probability ratio without inserting an unproved target-probability reflection hypothesis.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: reverse the same original finite summation and apply the independently proved exact reflection of the actual support probabilities and the actual finite relative gap products. -/
theorem comparisonNormalizer_reflection (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    comparisonNormalizer a b ha hb n=comparisonNormalizer b a hb ha n := by
  unfold comparisonNormalizer
  calc
    _ = ∑j:Fin (n+1),(supportMeasure a b ha hb n).weight j.rev*relativeGapProduct a b ha hb n j.rev :=
      (Equiv.sum_comp Fin.revPerm (fun j => (supportMeasure a b ha hb n).weight j*relativeGapProduct a b ha hb n j)).symm
    _ = _ := by simp_rw [supportMeasure_weight_reflection,relativeGapProduct_reflection]

/-- The actual original target/support probability ratio reflects exactly at every valid scalar spectral index.
Use: comparisonWeightAt_reflected_tendsto reuses the complete actual right-edge limit for the exchanged parameters, proving the printed left-edge limit too.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: both original ratios have the independently proved exact relative-gap numerator and literal support-weighted denominator. Their actual finite reflections have both been proved, and the true scalar left index is exactly the genuine finite reversal of the right index. -/
theorem comparisonWeightAt_reflection {a b:ℝ} (ha:-1<a) (hb:-1<b) {n k:ℕ} (hk:k≤n) :
    comparisonWeightAt a b ha hb n (n-k)=comparisonWeightAt b a hb ha n k := by
  -- The true probability formula, not a second independently defined reflected target, supplies the equality.
  have hk' : k<n+1 := by omega
  have hnk : n-k<n+1 := by omega
  simp only [comparisonWeightAt,dite_eq_left hk',dite_eq_left hnk,comparisonWeight_ratio]
  change relativeGapProduct a b ha hb n ⟨n-k,hnk⟩/comparisonNormalizer a b ha hb n=
    relativeGapProduct b a hb ha n ⟨k,hk'⟩/comparisonNormalizer b a hb ha n
  have hi : (⟨n-k,hnk⟩:Fin (n+1))=(⟨k,hk'⟩:Fin (n+1)).rev := by apply Fin.ext; simp only [Fin.val_rev]; omega
  rw [hi,relativeGapProduct_reflection,comparisonNormalizer_reflection]

/-- Every fixed reflected actual target/support weight ratio has exactly the original opposite-edge norming-ratio limit.
Use: the alternating beta edge in the full target Gram and Cholesky limits has its true source normalization, completing the fixed-index assertions of Weight ratio(b).
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: at every eventual valid index the ratio is exactly the proved reflected ratio for the exchanged endpoint parameters. Apply the unconditional right-edge weight-ratio limit for those original exchanged parameters. -/
theorem comparisonWeightAt_reflected_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => comparisonWeightAt a b ha hb n (n-k)) atTop (𝓝 (normingRatio b hb k)) := by
  apply (comparisonWeightAt_tendsto hb ha k).congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (comparisonWeightAt_reflection ha hb hn).symm

end
end jacobi.Comparison
