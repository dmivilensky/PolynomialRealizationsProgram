import chebyshev2.Filters.FredholmCurve

/-!
Article: chebyshev2, Proposition 3.
Fredholm Limits.
Use: `chebyshev2.Filters.leftLogDeterminant_right_limit` feeds
`chebyshev2.Filters.log_transmission_eq_logDeterminant` (Fredholm--Jost identity at the level of
the actual spectral logarithm).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.HalfLine
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `|leftLogDeterminant hm hn s x| ≤ s/2*cumulative m x`.

Use: `chebyshev2.Filters.leftLogDeterminant_left_limit` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto
(leftLogDeterminant hm hn s) atBot (𝓝 0)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.leftDensity_integrable`,
`chebyshev2.HalfLine.leftDensity_nonneg`,
`chebyshev2.Continuum.logDeterminant_distance` with the arguments shown in the proof.
-/
theorem leftLogDeterminant_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : |leftLogDeterminant hm hn s x| ≤ s/2*cumulative m x := by
  -- Use the identities/estimates `chebyshev2.HalfLine.leftDensity_integrable`,
  -- `chebyshev2.HalfLine.leftDensity_nonneg`,
  -- `chebyshev2.Continuum.logDeterminant_distance` with the arguments shown in the proof.
  let D := densitySpectralData (leftDensity_integrable hm x) (leftDensity_nonneg hn x)
  have h0 : logDeterminant (fun _ : ℕ => (0:ℝ)) s=0 := by simp [logDeterminant]
  have h := logDeterminant_distance D.eigenvalue_summable summable_zero D.eigenvalue_nonneg
    (fun _ => le_rfl) hs
  rw [h0,sub_zero] at h
  simp only [sub_zero,abs_of_nonneg (D.eigenvalue_nonneg _)] at h
  have hmass : (∑' i, D.eigenvalue i)=cumulative m x := by
    rw [density_kernel_eigenvalue_eq (leftDensity_integrable hm x) (leftDensity_nonneg hn x) D,
      kernelEigenvalue_mass]
    rw [leftDensity,integral_indicator measurableSet_Iio,← integral_Iic_eq_integral_Iio]
    rfl
  rw [hmass] at h
  exact h

/--
Convergence along the specified source filter to the specified limit: `Tendsto
(leftLogDeterminant hm hn s) atBot (𝓝 0)`.

Use: `chebyshev2.Filters.leftLogDeterminant_eq_log_truncatedTransmission` uses this limit
to establish the identity `leftLogDeterminant hm hn s x=log (truncatedTransmission s m x)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem leftLogDeterminant_left_limit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (leftLogDeterminant hm hn s) atBot (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (cumulative_left_limit m).const_mul (s/2)
  simp only [mul_zero] at h
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun x => by simpa only [Real.norm_eq_abs] using leftLogDeterminant_bound hm hn hs x) h

/--
Convergence along the specified source filter to the specified limit: `Tendsto (leftTraceClass
m) atTop (𝓝 (traceClassDensityOperator m))`.

Use: `chebyshev2.Filters.leftLogDeterminant_right_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto
(leftLogDeterminant hm hn s) atTop (𝓝 (logDeterminant (kernelEigenvalue hm hn) s))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem leftTraceClass_right_limit {m : ℝ → ℝ} (hm : Integrable m) :
    Tendsto (leftTraceClass m) atTop (𝓝 (traceClassDensityOperator m)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hg := traceClassDensity_integrable hm
  have hlim := (intervalIntegral_tendsto_integral_Ioi (0:ℝ) hg.integrableOn tendsto_id).const_add
    (leftTraceClass m 0)
  have he : (fun x : ℝ => leftTraceClass m 0+∫ t in (0:ℝ)..x, m t • traceClassFeature t)=
      leftTraceClass m := by
    funext x
    rw [← leftTraceClass_sub hm]
    abel
  have hval : leftTraceClass m 0+(∫ t in Ioi (0:ℝ), m t • traceClassFeature t)=
      traceClassDensityOperator m :=
    intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn
  change Tendsto (fun x : ℝ => leftTraceClass m 0+∫ t in (0:ℝ)..x, m t • traceClassFeature t)
    atTop (𝓝 (leftTraceClass m 0+∫ t in Ioi (0:ℝ), m t • traceClassFeature t)) at hlim
  rwa [he,hval] at hlim

/--
Convergence along the specified source filter to the specified limit: `Tendsto
(leftLogDeterminant hm hn s) atTop (𝓝 (logDeterminant (kernelEigenvalue hm hn) s))`.

Use: `chebyshev2.Filters.log_transmission_eq_logDeterminant` uses this limit to establish
exact identity `log (transmission s m)=logDeterminant (kernelEigenvalue hm hn) s`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem leftLogDeterminant_right_limit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (leftLogDeterminant hm hn s) atTop
      (𝓝 (logDeterminant (kernelEigenvalue hm hn) s)) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  have hnorm := ((leftTraceClass_right_limit hm).sub_const (traceClassDensityOperator m)).norm.const_mul (s/2)
  simp only [sub_self,norm_zero,mul_zero] at hnorm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) hnorm
  have hW := (leftTraceClass m x-traceClassDensityOperator m).property.traceBound
  change TraceBound (leftTraceClass m x-traceClassDensityOperator m).val
    ‖leftTraceClass m x-traceClassDensityOperator m‖ at hW
  simp only [TraceClassOperator.val_sub,leftTraceClass_val hm,traceClassDensityOperator_val hm] at hW
  have h := logDeterminant_traceBound (densityOperator_isCompact (leftDensity_integrable hm x))
    (densityOperator_isCompact hm)
    (densityOperator_positive (leftDensity_integrable hm x) (leftDensity_nonneg hn x))
    (densityOperator_positive hm hn)
    (densitySpectralData (leftDensity_integrable hm x) (leftDensity_nonneg hn x))
    (densitySpectralData hm hn) hW hs
  rw [density_kernel_eigenvalue_eq hm hn (densitySpectralData hm hn)] at h
  simpa only [Real.norm_eq_abs,leftLogDeterminant] using h

end
end chebyshev2.Filters
