import jacobi.Support.TopScaleLimit
import jacobi.Support.SineGamma
import jacobi.Reference.NormingFormula

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
At each fixed spectral index, sine ratios tend to their linear ratios
and cosine ratios tend to one. The resulting finite product is exactly
the ratio of the original reference norming integrals.
Use: weightIncrement_limit and fixedWeight_ratio_limit evaluate the genuine support-weight product at every fixed spectral index.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- Every fixed shifted support sine quotient has its exact small-step limit.
Use: weightIncrement_limit and fixedWeight_ratio_limit evaluate the genuine support-weight product at every fixed spectral index.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Source: continuity of Real.sinc at zero.
Proof: factor both sines into argument times sinc. The actual positive step cancels, and the denominator sinc tends to one. -/
theorem fixed_sine_ratio_limit {a b : ℝ} (ha:-1<a) (hb:-1<b) (p:ℝ) {q:ℝ} (hq:q≠0) :
    Tendsto (fun n:ℕ => sin (p*step a b (n+1))/sin (q*step a b (n+1))) atTop (𝓝 (p/q)) := by
  -- Cancel the positive step only after factoring the continuous sinc terms.
  have hz := support_step_zero a b tendsto_id
  have hpz := hz.const_mul p
  have hqz := hz.const_mul q
  simp only [mul_zero] at hpz hqz
  have hp := continuous_sinc.continuousAt.tendsto.comp hpz
  have hq' := continuous_sinc.continuousAt.tendsto.comp hqz
  simp only [sinc_zero,Function.comp_def] at hp hq'
  have h := (hp.div hq' one_ne_zero).const_mul (p/q)
  simp only [div_self one_ne_zero,mul_one] at h
  apply (tendsto_congr ?_).mpr h
  intro n
  simp only [Pi.div_apply,id_eq]
  rw [sin_eq_mul_sinc,sin_eq_mul_sinc]
  field_simp [hq,(step_pos ha hb (show 0<n+1 by omega)).ne']

/-- Every fixed shifted support cosine quotient tends to one.
Use: weightIncrement_limit shows that the original beta-dependent cosine factors disappear from each fixed-index weight ratio.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Source: continuity of cosine at zero.
Proof: both actual arguments tend to zero; both cosines tend to one, so division is continuous at their genuine nonzero limit. -/
theorem fixed_cosine_ratio_limit (a b p q:ℝ) :
    Tendsto (fun n:ℕ => cos (p*step a b (n+1))/cos (q*step a b (n+1))) atTop (𝓝 (1:ℝ)) := by
  have hz := support_step_zero a b tendsto_id
  have hp := continuous_cos.continuousAt.tendsto.comp (hz.const_mul p)
  have hq := continuous_cos.continuousAt.tendsto.comp (hz.const_mul q)
  have h := hp.div hq (by simp)
  simp only [mul_zero,cos_zero,div_self one_ne_zero] at h
  apply (tendsto_congr ?_).mpr h
  intro n
  rfl

/-- The limiting fixed-index weight product is precisely the ratio of the actual reference norming integrals.
Use: fixedWeight_limit identifies every genuine support-weight limit with the printed reference norm, rather than leaving an unevaluated finite product.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: evaluate the original finite rising product by the Gamma recurrence and insert the already proved exact formulas for both genuine reference norming integrals. Every cancelled Gamma factor and the original normalization scalar is positive. -/
theorem fixed_weight_norming_ratio {a : ℝ} (ha:-1<a) (k:ℕ) :
    ((k:ℝ)+gamma a)/gamma a*(∏j∈Finset.range k,((j:ℝ)+2*gamma a)/((j:ℝ)+1))=
      norming a 0/norming a k := by
  -- Preserve the exact Gamma amplitude; it is the source's actual norm integral.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hk0 := Nat.cast_nonneg k (α:=ℝ)
  rw [risingRatio_gamma (by positivity),norming_formula ha,norming_formula ha]
  simp only [Nat.cast_zero,zero_add,Gamma_one,mul_one]
  field_simp [hg.ne',(by positivity : (k:ℝ)+gamma a≠0),
    (Gamma_pos_of_pos (by positivity : 0<2*gamma a)).ne',
    (Gamma_pos_of_pos (by positivity : 0<(k:ℝ)+2*gamma a)).ne',
    (Gamma_pos_of_pos (by positivity : 0<(k:ℝ)+1)).ne',(normConstant_pos ha).ne']

end
end jacobi.Support
