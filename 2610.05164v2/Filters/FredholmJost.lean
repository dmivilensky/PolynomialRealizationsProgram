import «2610.05164v2».Filters.FredholmDerivative
import «2610.05164v2».Filters.FredholmLimits
import «2610.05164v2».Filters.TransmissionPrimitive
import «2610.05164v2».Filters.OutsideSupport

/-!
Article: 2610.05164v2, Proposition 3.
Proposition 3(ii): the integral of the literal nonlinear filter is H_m.
Use: `«2610.05164v2».Filters.nonlinear_mass_eq_logDeterminant` feeds
`«2610.05164v2».Comparison.Profile.signed_determinant_comparison` (signed determinant comparison).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The two spatial logarithms have identical AE derivatives and the same normalization at the left
endpoint.

Exact identity `leftLogDeterminant hm hn s x=log (truncatedTransmission s m x)`.

Use: `«2610.05164v2».Filters.log_transmission_eq_logDeterminant` uses this identity to
establish exact identity `log (transmission s m)=logDeterminant (kernelEigenvalue hm hn) s`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem leftLogDeterminant_eq_log_truncatedTransmission {m : ℝ → ℝ}
    (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    leftLogDeterminant hm hn s x=log (truncatedTransmission s m x) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let f : ℝ → ℝ := fun x => leftLogDeterminant hm hn s x-log (truncatedTransmission s m x)
  have hconst (y : ℝ) : f y=f 0 := by
    have hH := leftLogDeterminant_locallyAC hm hn hs 0 y
    have hT := log_truncatedTransmission_locallyAC hm hn hs 0 y
    have hd : ∀ᵐ t, t ∈ uIcc (0:ℝ) y → HasDerivAt f 0 t := by
      filter_upwards [hH.ae_differentiableAt,leftTraceClass_derivative hm,
        log_truncatedTransmission_derivative hm hn hs] with t ht hD hT' hmem
      have h := (leftLogDeterminant_hasDerivAt hm hn hs hD (ht hmem)).sub hT'
      change HasDerivAt f ((s*m t/(2+nonlinear s m t))-(s*m t/(2+nonlinear s m t))) t at h
      simpa only [sub_self] using h
    obtain ⟨c,hc⟩ := (hH.sub hT).const_of_ae_hasDerivAt_zero hd
    exact (hc y (by simp)).trans (hc 0 (by simp)).symm
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto f atBot (𝓝 0) := by
    have hlog := (Real.continuousAt_log (show (1:ℝ) ≠ 0 by norm_num)).tendsto.comp
      (truncatedTransmission_left_limit s m)
    change Tendsto (fun x => leftLogDeterminant hm hn s x-log (truncatedTransmission s m x))
      atBot (𝓝 0)
    simpa only [Function.comp_def,log_one,sub_zero] using
      (leftLogDeterminant_left_limit hm hn hs).sub hlog
  have hf : f=(fun _ => f 0) := funext hconst
  rw [hf] at hl
  have hz : f 0=0 := tendsto_nhds_unique tendsto_const_nhds hl
  have hx := hconst x
  rw [hz] at hx
  exact sub_eq_zero.mp hx

/--
Fredholm--Jost identity at the level of the actual spectral logarithm. Both sides keep their
original, independent definitions.

Exact identity `log (transmission s m)=logDeterminant (kernelEigenvalue hm hn) s`.

Use: `«2610.05164v2».Filters.nonlinear_mass_eq_logDeterminant` rewrites with this identity to
establish exact identity `(∫ x, nonlinear s m x)=logDeterminant (kernelEigenvalue hm hn) s`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem log_transmission_eq_logDeterminant {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    log (transmission s m)=logDeterminant (kernelEigenvalue hm hn) s := by
  -- Record the convergence hlog with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlog : Tendsto (fun x => log (truncatedTransmission s m x)) atTop
      (𝓝 (log (transmission s m))) :=
    (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans_le (transmission_ge_one hm hn hs)))).tendsto.comp
      (truncatedTransmission_right_limit hm hn hs)
  have hlim := leftLogDeterminant_right_limit hm hn hs
  have he : leftLogDeterminant hm hn s=(fun x => log (truncatedTransmission s m x)) :=
    funext (leftLogDeterminant_eq_log_truncatedTransmission hm hn hs)
  rw [he] at hlim
  exact tendsto_nhds_unique hlog hlim

/--
C.1's Fredholm--Jost formula for every nonnegative integrable density, including zero density
and zero scale.

Exact identity `transmission s m=fredholmDeterminant (kernelEigenvalue hm hn) s`.

Use: `«2610.05164v2».Filters.jost_right_limit_fredholm` rewrites with this identity to
establish convergence along the specified source filter to the specified limit: `Tendsto (jost
s m) atTop (𝓝 (fredholmDeterminant (kernelEigenvalue hm hn) s))`.

Article: 2610.05164v2, Proposition 3.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.fredholmDeterminant_eq_exp`,
`«2610.05164v2».Continuum.PositiveSpectralData.eigenvalue_summable`,
`«2610.05164v2».Continuum.PositiveSpectralData.eigenvalue_nonneg` with the arguments shown in
the proof.
-/
theorem transmission_eq_fredholmDeterminant {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    transmission s m=fredholmDeterminant (kernelEigenvalue hm hn) s := by
  rw [fredholmDeterminant_eq_exp (a := kernelEigenvalue hm hn) (kernelSpectralData hm hn).eigenvalue_summable
    (kernelSpectralData hm hn).eigenvalue_nonneg hs,← log_transmission_eq_logDeterminant hm hn hs,
    exp_log (zero_lt_one.trans_le (transmission_ge_one hm hn hs))]

/--
Proposition 3(ii): the integral of the literal nonlinear filter is H_m.

Exact identity `(∫ x, nonlinear s m x)=logDeterminant (kernelEigenvalue hm hn) s`.

Use: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` rewrites with this
identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_mass`,
`«2610.05164v2».Filters.log_transmission_eq_logDeterminant` with the arguments shown in the
proof.
-/
theorem nonlinear_mass_eq_logDeterminant {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, nonlinear s m x)=logDeterminant (kernelEigenvalue hm hn) s := by rw [nonlinear_mass hm hn hs,log_transmission_eq_logDeterminant hm hn hs]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (jost s m) atTop
(𝓝 (fredholmDeterminant (kernelEigenvalue hm hn) s))`.

Use: `«2610.05164v2».Filters.jost_right_limit_exp_logDeterminant` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (jost s m) atTop
(𝓝 (exp (logDeterminant (kernelEigenvalue hm hn) s)))`.

Article: 2610.05164v2, Proposition 3.

Proof: Use the identities/estimates
`«2610.05164v2».Filters.transmission_eq_fredholmDeterminant`,
`«2610.05164v2».Filters.jost_right_limit` with the arguments shown in the proof.
-/
theorem jost_right_limit_fredholm {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (jost s m) atTop
      (𝓝 (fredholmDeterminant (kernelEigenvalue hm hn) s)) := by
  rw [← transmission_eq_fredholmDeterminant hm hn hs]
  exact jost_right_limit hm hn hs

end
end «2610.05164v2».Filters
