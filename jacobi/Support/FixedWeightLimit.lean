import jacobi.Support.WeightFormula
import jacobi.Support.FixedSineLimits
import jacobi.Support.TopWeightLimit

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The exact sine-product probability formula propagates the proved first
weight limit to every fixed index. The limit is identified with the actual
reference norming integral, independently of the general polynomial edge
limit. Out-of-range scalar indices are extended by zero solely to state
ordinary sequence limits.
Use: fixedWeight_ratio_limit and fixedWeight_limit state the complete source limits without carrying a dimension-dependent finite-index proof through the filter.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual support probability as a scalar-indexed sequence, extended by zero outside its finite dimension.
Use: fixedWeight_ratio_limit and fixedWeight_limit state the complete source limits without carrying a dimension-dependent finite-index proof through the filter.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def naturalWeight (a b : ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) : ℝ :=
  if hk:k<n+1 then (naturalMeasure a b ha hb n).weight ⟨k,hk⟩ else 0

/-- Every fixed original sine-cosine weight increment has the exact beta-independent limiting rising factor.
Use: fixedWeight_ratio_limit evaluates the original finite product in the genuine spectral probability formula.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: split the exact original increment into its sine and cosine quotients. The former tends to the ratio of its two positive linear arguments; the latter tends to one. The actual half-step normalization cancels exactly. -/
theorem weightIncrement_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (j:ℕ) :
    Tendsto (fun n:ℕ => weightIncrement a b (n+1) j) atTop
      (𝓝 (((j:ℝ)+2*gamma a)/((j:ℝ)+1))) := by
  -- Both vanishing sines are normalized by sinc before passing to the limit.
  have hj := Nat.cast_nonneg j (α:=ℝ)
  have hs := fixed_sine_ratio_limit ha hb (((j:ℝ)+2*gamma a)/2)
    (show (((j:ℝ)+1)/2)≠0 by positivity)
  have hc := fixed_cosine_ratio_limit a b (((j:ℝ)+gamma a+gamma b)/2)
    (((j:ℝ)+1+gamma a-gamma b)/2)
  have h := hs.mul hc
  simp only [mul_one,div_div_div_cancel_right₀ (by norm_num : (2:ℝ)≠0)] at h
  convert h using 1
  funext n
  simp only [weightIncrement]
  have he (p:ℝ) : p/2*step a b (n+1)=p*step a b (n+1)/2 := by ring
  simp_rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The ratio of two actual original support probabilities is precisely their explicit sine-product ratio.
Use: fixedWeight_ratio_limit applies scalar limit theorems directly to the same original finite spectral measure.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the complete probability formula has one common positive normalizer. Cancel it and use the exact empty product at the first original node. -/
theorem naturalWeight_ratio {a b:ℝ} (ha:-1<a) (hb:-1<b) {n k:ℕ} (hk:k≤n) :
    naturalWeight a b ha hb n k/naturalWeight a b ha hb n 0=
      sin (jacobi.Jacobi.modelAngle a b (n+1) k)/
        sin (jacobi.Jacobi.modelAngle a b (n+1) 0)*
          ∏j∈Finset.range k,weightIncrement a b (n+1) j := by
  obtain ⟨Z,hZ,hformula⟩ := naturalMeasure_weight_formula ha hb n
  simp only [naturalWeight,dite_eq_left (show k<n+1 by omega),dite_eq_left (show 0<n+1 by omega)]
  rw [(hformula ⟨k,by omega⟩).1,(hformula ⟨0,by omega⟩).1]
  simp only [weightFactor,Finset.prod_range_zero,mul_one]
  field_simp [hZ.ne']

/-- The ratio of every fixed original support weight to its first weight converges to the exact ratio of the actual reference norms.
Use: fixedWeight_limit discharges every remaining fixed-index norming asymptotic from the already proved actual top probability limit.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: apply the exact normalization-free sine product for all sufficiently large original dimensions. The angular sine ratio has its linear limit and every fixed increment has its proved rising-factor limit. The Gamma identity identifies the resulting actual finite product with the genuine reference norm ratio. -/
theorem fixedWeight_ratio_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => naturalWeight a b ha hb n k/naturalWeight a b ha hb n 0)
      atTop (𝓝 (norming a 0/norming a k)) := by
  -- All fixed-index statements concern the original finite measure once the index exists.
  have hg : 0<gamma a := (parameter_pos ha hb).1
  have hs := fixed_sine_ratio_limit ha hb ((k:ℝ)+gamma a) hg.ne'
  have hp := tendsto_finsetProd (Finset.range k) (fun j _ => weightIncrement_limit ha hb j)
  have h := hs.mul hp
  rw [fixed_weight_norming_ratio ha k] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [naturalWeight_ratio ha hb hn,modelAngle_step,modelAngle_step]
  simp only [Nat.cast_zero,zero_add]

/-- Every fixed actual original support probability has the full printed exact positive norming limit.
Use: the target/support weight-ratio limit and the two-edge Gram expansion use every actual reference norming coefficient, without assuming a support polynomial convergence certificate.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: multiply the independently proved original top probability limit by the exact fixed-index probability-ratio limit. The actual first norm cancels; both it and the Gamma amplitude are strictly positive. -/
theorem fixedWeight_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => (n:ℝ)^(1+2*gamma a)*naturalWeight a b ha hb n k)
      atTop (𝓝 ((topAmplitudeSquare a b*norming a k)⁻¹)) := by
  -- The normalization is already proved at the first node; this step introduces no new numerical or limit assumption.
  have h := (topWeight_limit ha hb).mul (fixedWeight_ratio_limit ha hb k)
  have he : (topAmplitudeSquare a b*norming a 0)⁻¹*(norming a 0/norming a k)=
      (topAmplitudeSquare a b*norming a k)⁻¹ := by
    field_simp [(topAmplitudeSquare_pos ha hb).ne',(norming_pos ha 0).ne',(norming_pos ha k).ne']
  rw [he] at h
  apply (tendsto_congr ?_).mpr h
  intro n
  have hz : (⟨0,show 0<n+1 by omega⟩:Fin (n+1))=0 := by apply Fin.ext; rfl
  simp only [naturalWeight,dite_eq_left (show 0<n+1 by omega),hz]
  field_simp [((naturalMeasure a b ha hb n).positive 0).ne']

end
end jacobi.Support
