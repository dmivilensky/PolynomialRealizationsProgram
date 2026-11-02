import jacobi.Comparison.WeightProductBounds
import jacobi.Support.EdgeWeightMass

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The literal support-weighted relative gap normalizer is positive,
uniformly separated from zero and equal to 1+o(1/N). All probabilities
and products belong to the actual original matrices. Dominated
convergence of the inverse-square edge mass gives the printed error
rate without an additional asymptotic premise.
Use: comparisonWeight_error retains the literal denominator of comparisonWeight_ratio and controls its deviation from one.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Support
open scoped Topology

/-- The exact original support-weighted finite relative gap normalizer.
Use: comparisonWeight_error retains the literal denominator of comparisonWeight_ratio and controls its deviation from one.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def comparisonNormalizer (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : ℝ :=
  ∑k,(supportMeasure a b ha hb n).weight k*relativeGapProduct a b ha hb n k

/-- The original finite relative-gap normalizer is strictly positive in every dimension.
Use: comparisonNormalizer_bounds and comparisonWeight_error divide only by the actual nonzero normalizer of the two genuine spectral measures.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: each actual support probability and relative gap product is positive; the original dimension is nonempty. -/
theorem comparisonNormalizer_pos (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    0<comparisonNormalizer a b ha hb n := by
  exact sum_pos (fun k _ => mul_pos ((supportMeasure a b ha hb n).positive k)
    (relativeGapProduct_pos a b ha hb n k)) univ_nonempty

/-- The actual finite normalizer is uniformly positive and bounded at large dimension.
Use: comparisonWeight_error transfers the small actual gap-product perturbation to the normalized original probability ratio.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: average the already proved positive lower and upper product bounds against the original support probability, whose total mass is exactly one. -/
theorem comparisonNormalizer_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,
      c≤comparisonNormalizer a b ha hb n ∧ comparisonNormalizer a b ha hb n≤C := by
  -- Averaging constant bounds preserves them because the actual support measure has mass exactly one.
  obtain ⟨c,C,D,hc,hC,hD,hbound⟩ := relativeGapProduct_bounds ha hb
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound] with n hn
  have hp := (supportMeasure a b ha hb n).probability
  have hl := sum_le_sum (fun k (_:k∈univ) =>
    mul_le_mul_of_nonneg_left (hn k).1 ((supportMeasure a b ha hb n).positive k).le)
  have hu := sum_le_sum (fun k (_:k∈univ) =>
    mul_le_mul_of_nonneg_left (hn k).2.1 ((supportMeasure a b ha hb n).positive k).le)
  rw [← sum_mul,hp,one_mul] at hl hu
  exact ⟨hl,hu⟩

/-- The original normalizer error is bounded by the actual inverse-square edge mass and the original logarithmic bulk error.
Use: comparisonNormalizer_error multiplies this genuine bound by the true matrix size and proves the exact little-o normalization error required in Weight ratio(b).
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: use the exact original probability mass to write S_n-1 as the support average of R_(n,k)-1. The triangle inequality and the proved actual product error apply term by term. Sum the inverse-square term and the common bulk term separately. -/
theorem comparisonNormalizer_estimate {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃D:ℝ,0<D ∧ ∀ᶠn:ℕ in atTop,
      |comparisonNormalizer a b ha hb n-1|≤D*((∑k:Fin (n+1),
        (supportMeasure a b ha hb n).weight k/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2)+
          log ((n:ℝ)+1)/((n:ℝ)+1)^2) := by
  -- The normalizer is the same literal weighted sum as in the exact probability ratio.
  obtain ⟨c,C,D,hc,hC,hD,hbound⟩ := relativeGapProduct_bounds ha hb
  refine ⟨D,hD,?_⟩
  filter_upwards [hbound] with n hn
  let w := (supportMeasure a b ha hb n).weight
  let R := relativeGapProduct a b ha hb n
  have hp : ∑k,w k=1 := (supportMeasure a b ha hb n).probability
  have he : comparisonNormalizer a b ha hb n-1=∑k,w k*(R k-1) := by
    simp_rw [mul_sub,mul_one]
    rw [sum_sub_distrib,hp]
    rfl
  rw [he]
  calc
    _ ≤ ∑k,|w k*(R k-1)| := abs_sum_le_sum_abs _ _
    _ = ∑k,w k*|R k-1| := by
      apply sum_congr rfl
      intro k _
      rw [abs_mul,abs_of_pos ((supportMeasure a b ha hb n).positive k)]
    _ ≤ ∑k,w k*(D*(1/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2+log ((n:ℝ)+1)/((n:ℝ)+1)^2)) :=
      sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hn k).2.2 ((supportMeasure a b ha hb n).positive k).le)
    _ = _ := by
      simp_rw [mul_add]
      rw [sum_add_distrib]
      have h₁ : (∑k,w k*(D*(1/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2)))=
          D*(∑k,w k/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        ring
      rw [h₁,← sum_mul,hp,one_mul]

/-- The actual original relative-gap normalizer differs from one by little-o of the reciprocal true matrix size.
Use: comparisonWeight_error constructs a single index-independent epsilon_N with N*epsilon_N->0, exactly as required for the uniform Gram comparison in jacobi.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: multiply the proved actual normalizer estimate by N. The independently proved complete two-edge weighted mass tends to zero. The remaining term is log(N)/N, whose limit is the community logarithm asymptotic. Squeeze the nonnegative original normalizer error. -/
theorem comparisonNormalizer_error {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ => ((n:ℝ)+1)*|comparisonNormalizer a b ha hb n-1|) atTop (𝓝 0) := by
  -- Both limits concern the original growing matrix dimension, not an auxiliary fixed spectral truncation.
  obtain ⟨D,hD,hbound⟩ := comparisonNormalizer_estimate ha hb
  have hN : Tendsto (fun n:ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n:ℕ => log ((n:ℝ)+1)/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero,Function.comp_def] using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN
  have ht := ((edge_weight_mass ha hb).add hlog).const_mul D
  simp only [add_zero,mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (by positivity) (abs_nonneg _))) _ ht
  filter_upwards [hbound] with n hn
  have h := mul_le_mul_of_nonneg_left hn (show 0≤(n:ℝ)+1 by positivity)
  convert h using 1
  field_simp

end
end jacobi.Comparison
