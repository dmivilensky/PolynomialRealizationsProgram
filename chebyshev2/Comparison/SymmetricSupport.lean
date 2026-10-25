import chebyshev2.Comparison.SymmetricTrace

/-!
Article: chebyshev2, Theorem 3.6.
The support-to-center versions printed in Lemma 14, with the density already translated so that its
symmetry center is zero.
Use: `chebyshev2.Comparison.symmetric_square_trace_support` feeds
`chebyshev2.DualCertificate.NormalizedCalibration.S_actual` (S actual).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Comparison
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Filters chebyshev2.Continuum chebyshev2.GroundState
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(∫ x in Iic (0:ℝ), f x)=∫ x in a..0, f x`.

Use: `chebyshev2.Comparison.symmetric_logDeterminant_support` rewrites with this identity
to establish `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in
a..0, nonlinear s m x)+log (1+nonlinear s m 0)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem halfLine_eq_support_interval {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ)
    (hz : ∀ x ≤ a, f x=0) : (∫ x in Iic (0:ℝ), f x)=∫ x in a..0, f x := by
  have he : (∫ x in Iic a, f x)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact hz x hx
  have h := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := (0:ℝ)) hf.integrableOn hf.integrableOn
  simpa only [he,sub_zero] using h

variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
  (hc : Continuous m) (hSym : ∀ x, m (-x)=m x)
include hc hSym

/--
The precise assertion is `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in a..0, nonlinear
s m x)+log (1+nonlinear s m 0)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.H_actual` rewrites with this
identity to establish the identity `N.H hκ s=logDeterminant (kernelEigenvalue
((N.calibration.comparisonSpeed hκ).density_integrable hκ) ((N.calibration.comparisonSpeed
hκ).density_nonneg hκ)) s`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Comparison.symmetric_logDeterminant`,
`chebyshev2.Comparison.halfLine_eq_support_interval`,
`chebyshev2.Filters.nonlinear_integrable` with the arguments shown in the proof.
-/
theorem symmetric_logDeterminant_support {s : ℝ} (hs : 0 ≤ s) (a : ℝ)
    (hz : ∀ x ≤ a, m x=0) :
    logDeterminant (kernelEigenvalue hm hn) s=
      2*(∫ x in a..0, nonlinear s m x)+log (1+nonlinear s m 0) := by
  rw [symmetric_logDeterminant hm hn hc hs hSym,
    halfLine_eq_support_interval (nonlinear_integrable hm hn hs) a
      (fun x hx => nonlinear_left_of_density_zero x s (fun t ht => hz t (ht.trans hx)))]

/--
The precise assertion is `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)= 2*(∫
x in a..0, (linear hm hn x)^2)+(linear hm hn 0)^2`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.S_actual` rewrites with this
identity to establish the identity `N.S hκ=∫ x,(chebyshev2.Filters.linear
((N.calibration.comparisonSpeed hκ).density_integrable hκ) ((N.calibration.comparisonSpeed
hκ).density_nonneg hκ) x)^2`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem symmetric_square_trace_support (a : ℝ) (hz : ∀ x ≤ a, m x=0) :
    (groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)=
      2*(∫ x in a..0, (linear hm hn x)^2)+(linear hm hn 0)^2 := by
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => (linear hm hn x)^2) := by
    simpa only [linear,mul_pow] using (causal_square_integrable hm hn).const_mul
      ((groundParameter hm hn)^2)
  have hz' (x : ℝ) (hx : x ≤ a) : (linear hm hn x)^2=0 := by
    have hj : (∫ t in Iic x, exp (2*t)*m t)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      change exp (2*t)*m t=0
      rw [hz t (ht.trans hx),mul_zero]
    simp [linear,causal,hj]
  rw [symmetric_square_trace hm hn hc hSym,halfLine_eq_support_interval hi a hz']

end
end chebyshev2.Comparison
