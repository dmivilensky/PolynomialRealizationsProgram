import jacobi.Support.FrequencyPowers

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The printed minimum envelope changes by at most the fixed factor
2^gamma on the original Cauchy circle. The small-frequency case is
handled without evaluating a negative power at zero.
Use: the actual frequency-circle comparison retains the same original minimum in the Cauchy estimate.
-/
namespace jacobi.Support
noncomputable section
open Real

/-- Scaling the second member of a nonnegative minimum gives the corresponding common positive-factor minimum bound.
Use: the actual frequency-circle comparison retains the same original minimum in the Cauchy estimate.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: bound the original minimum separately by the two entries of the scaled minimum. -/
theorem frequency_min_scale {x y z F:ℝ} (hx:0≤x) (hF:1≤F) (hz:z≤F*y) :
    min x z≤F*min x y := by
  rw [mul_min_of_nonneg _ _ (zero_le_one.trans hF)]
  refine le_min ?_ ((min_le_right _ _).trans hz)
  exact (min_le_left _ _).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hF hx)

/-- On the actual high-frequency Cauchy disc, the source's negative frequency power increases by at most 2^gamma.
Use: frequency_min_circle_high and the actual support derivative estimate keep the original theta-dependent decay uniformly on its Cauchy circle.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the original triangle inequality and genuine circle radius imply the positive half-frequency lower bound. Monotonicity of the negative original exponent and the exact positive-base power quotient give the stated factor. -/
theorem frequency_decay_circle {g r:ℝ} (hg:0≤g) {theta z:ℂ} (ht:theta≠0)
    (hr:2*r≤‖theta‖) (hz:‖z-theta‖≤r) :
    0<‖z‖ ∧ ‖z‖^(-g)≤(2:ℝ)^g*‖theta‖^(-g) := by
  -- The actual lower norm bound excludes zero before any original negative power is compared.
  have ht0 : 0<‖theta‖ := norm_pos_iff.mpr ht
  have htriangle : ‖theta‖≤‖z-theta‖+‖z‖ := by
    simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (theta-z) z
  have hhalf : ‖theta‖/2≤‖z‖ := by linarith only [htriangle,hr,hz]
  refine ⟨(half_pos ht0).trans_le hhalf,?_⟩
  calc
    _ ≤ (‖theta‖/2)^(-g) := rpow_le_rpow_of_nonpos (half_pos ht0) hhalf (neg_nonpos.mpr hg)
    _ = _ := by rw [div_rpow ht0.le (by norm_num : (0:ℝ)≤2),rpow_neg (x:=2) (by norm_num),div_inv_eq_mul,mul_comm]

/-- The actual printed minimum has the original common 2^gamma Cauchy-circle comparison in the high-frequency region.
Use: the support envelope's derivative bound applies Cauchy's formula with the same original minimum at the center frequency.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: combine the proved negative-power circle estimate with the nonnegative minimum scaling identity. -/
theorem frequency_min_circle_high {g r x:ℝ} (hg:0≤g) (hx:0≤x) {theta z:ℂ} (ht:theta≠0)
    (hr:2*r≤‖theta‖) (hz:‖z-theta‖≤r) :
    min x (‖z‖^(-g))≤(2:ℝ)^g*min x (‖theta‖^(-g)) :=
  frequency_min_scale hx (one_le_rpow (by norm_num) hg) (frequency_decay_circle hg ht hr hz).2

/-- At a genuine small center frequency, the original growth power is controlled by 2^gamma times the exact printed minimum.
Use: the support derivative's small-frequency Cauchy circle uses the original transition bound even when a circle point is zero.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: the genuine scaled-frequency product is at most two, so its original power is bounded by 2^gamma times the frequency decay; the same factor is at least one. -/
theorem frequency_min_circle_low {g x:ℝ} (hg:0≤g) (hx:0<x) {theta:ℂ} (ht:theta≠0)
    (hscale:‖theta‖*x≤2) :
    x^g≤(2:ℝ)^g*min (x^g) (‖theta‖^(-g)) := by
  rw [mul_min_of_nonneg _ _ (rpow_nonneg (by norm_num : (0:ℝ)≤2) _)]
  refine le_min ?_ (frequency_power_bound (norm_pos_iff.mpr ht) hx.le hg hscale)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_rpow (by norm_num : (1:ℝ)≤2) hg) (rpow_pos_of_pos hx g).le

end
end jacobi.Support
