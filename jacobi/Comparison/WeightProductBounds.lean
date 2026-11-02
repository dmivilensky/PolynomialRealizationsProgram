import jacobi.Comparison.WeightLogBound
import jacobi.Reference.NormingBounds

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
Exponentiation of the full original finite logarithm estimate gives
positive uniform bounds and the required inverse-square plus bulk error
for the actual relative gap products. These are the same products in the
exact original probability-normalization identity.
Use: comparisonNormalizer_error and comparisonWeight_error turn the exact original gap-product normalization into the quantitative probability comparison needed for the two-edge Gram limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter
open scoped Topology

/-- The genuine finite relative gap products are uniformly positive and bounded, with the complete printed deviation estimate.
Use: comparisonNormalizer_error and comparisonWeight_error turn the exact original gap-product normalization into the quantitative probability comparison needed for the two-edge Gram limit.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: each original edge index is at least one and log(N)/N^2 is at most one. Thus the proved logarithm estimate is uniformly bounded. Monotonicity of the real exponential gives both positive bounds; the community exponential remainder inequality gives the full small deviation, preserving the inverse-square and bulk terms. -/
theorem relativeGapProduct_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C D:ℝ,0<c ∧ 0<C ∧ 0<D ∧ ∀ᶠn:ℕ in atTop,∀k:Fin (n+1),
      c≤relativeGapProduct a b ha hb n k ∧ relativeGapProduct a b ha hb n k≤C ∧
      |relativeGapProduct a b ha hb n k-1|≤
        D*(1/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2+log ((n:ℝ)+1)/((n:ℝ)+1)^2) := by
  -- The positive constants bound the literal original product at every growing spectral index.
  obtain ⟨L,hL,hbound⟩ := comparisonWeight_log_bound ha hb
  refine ⟨exp (-2*L),exp (2*L),L*exp (2*L),exp_pos _,exp_pos _,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro k
  let R := relativeGapProduct a b ha hb n k
  let N : ℝ := (n:ℝ)+1
  let d : ℝ := jacobi.Jacobi.edgeIndex (n+1) k.val
  have hd : 1≤d := by
    dsimp [d,jacobi.Jacobi.edgeIndex]
    exact_mod_cast (show 1≤min (k.val+1) (n+1-k.val) by omega)
  have hN : 1≤N := by dsimp [N]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hN0 : 0<N := by linarith
  have hlogN : 0≤log ((n:ℝ)+1) := log_nonneg hN
  have hlog := log_le_sub_one_of_pos hN0
  have hbulk : log N/N^2≤1 := (div_le_one (sq_pos_of_pos hN0)).mpr (by nlinarith)
  have hedge : 1/d^2≤1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hlogs : |log R|≤2*L := by
    have h := hn k
    change |log R|≤L*(1/d^2+log N/N^2) at h
    have hu := mul_le_mul_of_nonneg_left (add_le_add hedge hbulk) hL.le
    linarith
  have he : exp (log R)=R := exp_log (relativeGapProduct_pos a b ha hb n k)
  refine ⟨?_,?_,?_⟩
  · change exp (-2*L)≤R
    rw [← he]
    exact exp_le_exp.mpr (by linarith only [(abs_le.mp hlogs).1])
  · change R≤exp (2*L)
    rw [← he]
    exact exp_le_exp.mpr (abs_le.mp hlogs).2
  · have h := (jacobi.Reference.exp_sub_one_bound (log R)).trans
      (mul_le_mul (hn k) (exp_le_exp.mpr hlogs) (exp_pos _).le
        (by positivity : 0≤L*(1/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2+log ((n:ℝ)+1)/((n:ℝ)+1)^2)))
    rw [he] at h
    convert h using 1
    ring

end
end jacobi.Comparison
