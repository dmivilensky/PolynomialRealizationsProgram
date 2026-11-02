import jacobi.Comparison.WeightReflection
import jacobi.Reference.NormingWeights

/-!
Article: jacobi, Proposition C.3.
Every actual target spectral probability has its full printed edge
asymptotic, with the genuine matrix-size normalization, original Gamma
amplitude and reciprocal characteristic-derivative weight. The proof
uses the complete actual target/support ratio limit and the independently
proved support probability limit; it needs no polynomial edge-limit or
eigenvector-convergence premise. Theorem 2.1 remain separate.
Use: targetWeight_limit states Theorem 2.1 for the original target measure without a dimension-dependent finite index in the limit filter.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter jacobi.Support jacobi.Reference
open scoped Topology

/-- The actual original target probability on scalar spectral indices, extended by zero beyond its genuine finite dimension.
Use: targetWeight_limit states Theorem 2.1 for the original target measure without a dimension-dependent finite index in the limit filter.
Article: jacobi, Proposition C.3.
-/
def targetWeight (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) : ℝ :=
  if hk:k<n+1 then (targetMeasure a b ha hb n).weight ⟨k,hk⟩ else 0

/-- Every actual target probability is exactly its original target/support ratio times its original support probability, also under zero padding.
Use: targetWeight_degree_limit combines the two independently proved genuine source limits, with the original probabilities rather than an auxiliary weight sequence.
Article: jacobi, Proposition C.3.
Proof: at a genuine original index the original support probability is strictly positive and cancels. Outside the actual finite dimension both original padded probabilities are zero and the padded ratio is one. -/
theorem targetWeight_factor (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) :
    targetWeight a b ha hb n k=comparisonWeightAt a b ha hb n k*naturalWeight a b ha hb n k := by
  by_cases hk:k<n+1
  · simp only [targetWeight,comparisonWeightAt,naturalWeight,dite_eq_left hk]
    exact (div_mul_cancel₀ _ ((supportMeasure a b ha hb n).positive ⟨k,hk⟩).ne').symm
  · simp only [targetWeight,comparisonWeightAt,naturalWeight,dite_eq_right hk,mul_zero]

/-- The actual target probabilities have the original fixed-index limit in the finite-degree normalization.
Use: targetWeight_limit transfers this genuine limit to the article's true matrix size and printed kappa_U amplitude.
Article: jacobi, Proposition C.3.
Proof: multiply the independently proved full actual target/support ratio limit by the independently proved exact original support probability limit. The same positive original norm and amplitude give precisely the displayed limiting scalar. -/
theorem targetWeight_degree_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => (n:ℝ)^(1+2*gamma a)*targetWeight a b ha hb n k) atTop
      (𝓝 ((normingRatio a ha k/norming a k)/topAmplitudeSquare a b)) := by
  -- These two source probability limits are already proved independently of the general support-polynomial edge limit.
  have ht := (comparisonWeightAt_tendsto ha hb k).mul (fixedWeight_limit ha hb k)
  have he : normingRatio a ha k*(topAmplitudeSquare a b*norming a k)⁻¹=
      (normingRatio a ha k/norming a k)/topAmplitudeSquare a b := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at ht
  exact ht.congr' (Eventually.of_forall (fun n => by
    change comparisonWeightAt a b ha hb n k*((n:ℝ)^(1+2*gamma a)*naturalWeight a b ha hb n k)=
      (n:ℝ)^(1+2*gamma a)*targetWeight a b ha hb n k
    rw [targetWeight_factor]
    ring))

/-- The actual original support amplitude square has exactly the printed kappa_U^2*pi^(2*gamma_alpha) normalization.
Use: targetWeight_limit keeps precisely the same printed normalization as Theorem 2.1, rather than an unspecified positive amplitude.
Article: jacobi, Proposition C.3.
Proof: square the actual positive definition of kappa_U, use the true positive Gamma-amplitude square root and combine the two equal positive pi powers. -/
theorem topConstant_amplitude {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    topConstant a b^2*π^(2*gamma a)=topAmplitudeSquare a b := by
  -- The original Gamma amplitude and the actual positive branch are both retained.
  have hp : (π^gamma a)^2=π^(2*gamma a) := by rw [pow_two,← rpow_add pi_pos]; congr 1; ring
  rw [topConstant,div_pow,sq_sqrt (topAmplitudeSquare_pos ha hb).le,hp]
  exact div_mul_cancel₀ _ (rpow_pos_of_pos pi_pos _).ne'

/-- Every actual target spectral probability has the complete printed matrix-size asymptotic of Theorem 2.1.
Use: Theorem 2.1's target spectral measure converges with its exact original norming weight; all beta dependence is confined to the displayed original kappa_U amplitude.
Article: jacobi, Proposition C.3.
Proof: the true matrix size is the finite degree plus one. Its ratio to the positive degree tends to one, hence so does the corresponding positive-base real power. Multiply that exact factor by the proved actual target probability limit and use the original positive-base real-power multiplication identity. Finally insert the proved printed kappa_U normalization. -/
theorem targetWeight_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => ((n:ℝ)+1)^(1+2*gamma a)*targetWeight a b ha hb n k) atTop
      (𝓝 ((normingRatio a ha k/norming a k)/(topConstant a b^2*π^(2*gamma a)))) := by
  -- The final scale is the actual matrix dimension N=n+1, not only its asymptotically equivalent degree.
  have hratio : Tendsto (fun n:ℕ => ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 (1:ℝ)) := by
    have ht := tendsto_one_div_atTop_nhds_zero_nat.const_add (1:ℝ)
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
    field_simp [hn0]
  have ht := (hratio.rpow_const (p:=1+2*gamma a) (Or.inl one_ne_zero)).mul (targetWeight_degree_limit ha hb k)
  simp only [one_rpow,one_mul] at ht
  rw [topConstant_amplitude ha hb]
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  rw [← mul_assoc,← mul_rpow (by positivity : 0≤((n:ℝ)+1)/(n:ℝ)) hn0.le,div_mul_cancel₀ _ hn0.ne']

/-- The original reciprocal-characteristic-derivative probability rule passes to the complete printed continuum weight in Theorem 2.1.
Use: this identifies the exact original limiting target probability with Proposition C.2's genuine spectral norming weight, independently of the still required eigenvector and trace-norm limits in Theorem 2.1.
Article: jacobi, Proposition C.3.
Proof: substitute the independently proved original norming-ratio divided by its actual integral norm into the full genuine target probability limit. The original characteristic derivative is simple and nonzero by the earlier Bessel theory. -/
theorem targetWeight_characteristic_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    Tendsto (fun n:ℕ => ((n:ℝ)+1)^(1+2*gamma a)*targetWeight a b ha hb n k) atTop
      (𝓝 ((1/(2*π^2*normConstant a*‖deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)‖))/
        (topConstant a b^2*π^(2*gamma a)))) := by
  simpa only [normingRatio_div_norming ha k] using targetWeight_limit ha hb k

end
end jacobi.Comparison
