import jacobi.Support.TopSquareNormLimit
import jacobi.Support.WeightNorms

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The original top spectral probability has its full exact printed
positive limit. Both its polynomial normalization and continuum
constant are proved for the same original support chain.
Use: topWeight_normalization converts the actual full squared polynomial norm into the original power-normalized spectral probability.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The exact squared support scaling divided by the mesh size is the reciprocal original weight scaling.
Use: topWeight_normalization converts the actual full squared polynomial norm into the original power-normalized spectral probability.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: combine real powers of the same positive base; the exact exponents differ by negation. -/
theorem top_norm_scale {x:ℝ} (hx:0<x) (g:ℝ) :
    (x^(-g))^2/x=(x^(1+2*g))⁻¹ := by
  have hpow : (x^(-g))^2=x^(-2*g) := by
    rw [pow_two,← rpow_add hx]
    congr 1
    ring
  have hinv : x⁻¹=x^(-1:ℝ) := by rw [rpow_neg hx.le,rpow_one]
  rw [hpow,div_eq_mul_inv,hinv,← rpow_add hx,← rpow_neg hx.le]
  congr 1
  ring

/-- The actual original complete top-node polynomial squared norm is exactly the reciprocal power-normalized top spectral probability.
Use: topWeight_limit passes from the proved genuine squared-norm limit to the actual original positive spectral weight without an assumed normalization identity.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the genuine Christoffel identity gives the full original squared polynomial norm. Factor out the common original mesh power and apply its exact positive-base scaling identity. -/
theorem topWeight_normalization (a b:ℝ) (ha:-1<a) (hb:-1<b) {n:ℕ} (hn:0<n) :
    (∑j∈Finset.range (n+1),((n:ℝ)^(-gamma a)*topValue a b ha hb n j)^2)/(n:ℝ)=
      ((n:ℝ)^(1+2*gamma a)*(naturalMeasure a b ha hb n).weight 0)⁻¹ := by
  -- Both sides use the same original finite dimension, top cosine node and actual probability weight.
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hnorm := naturalMeasure_inverse_weight a b ha hb n 0
  have hnorm' : ((naturalMeasure a b ha hb n).weight 0)⁻¹=
      ∑j∈Finset.range (n+1),topValue a b ha hb n j^2 := by
    simp only [naturalNode,modelAngle_step,Fin.val_zero,Nat.cast_zero,zero_add] at hnorm
    change ((naturalMeasure a b ha hb n).weight 0)⁻¹=
      ∑i:Fin (n+1),(topValue a b ha hb n i)^2 at hnorm
    exact hnorm.trans (Fin.sum_univ_eq_sum_range (fun j => (topValue a b ha hb n j)^2) (n+1))
  calc
    _ = ((n:ℝ)^(-gamma a))^2/(n:ℝ)*(∑j∈Finset.range (n+1),topValue a b ha hb n j^2) := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      ring
    _ = _ := by rw [top_norm_scale hnr,← hnorm',mul_inv]

/-- The genuine original top support spectral probability has the complete exact printed positive norming limit.
Use: the support edge normalization and target/support weight comparison retain the original reference norm and actual Gamma amplitude at the first spectral level.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the actual complete squared polynomial norm has the independently proved printed positive limit. Its exact original Christoffel normalization is the reciprocal scaled spectral weight, so continuity of inversion at that strictly positive genuine norm gives the original probability limit. -/
theorem topWeight_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ => (n:ℝ)^(1+2*gamma a)*(naturalMeasure a b ha hb n).weight 0) atTop
      (𝓝 ((topAmplitudeSquare a b*norming a 0)⁻¹)) := by
  -- The actual original positive limiting norm discharges the sole nonzero premise of inversion.
  have hnorm : Tendsto (fun n:ℕ =>
      ((n:ℝ)^(1+2*gamma a)*(naturalMeasure a b ha hb n).weight 0)⁻¹) atTop
      (𝓝 (topAmplitudeSquare a b*norming a 0)) :=
    (topValue_square_norm_limit ha hb).congr' (by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
      exact topWeight_normalization a b ha hb hn)
  simpa only [inv_inv] using hnorm.inv₀ (mul_pos (topAmplitudeSquare_pos ha hb) (norming_pos ha 0)).ne'

end
end jacobi.Support
