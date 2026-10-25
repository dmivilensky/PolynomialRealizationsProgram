import chebyshev2.Filters.ContinuousDensity

/-!
Article: chebyshev2, Lemma 11.
Reflection invariance of the Fredholm logarithm, proved analytically by the two Jost solutions'
Wronskian.
Use: `chebyshev2.Filters.transmission_reflection` feeds
`chebyshev2.Comparison.Profile.rightJost_left_expansion` (right Jost left expansion).
Proof chain: `chebyshev2.Calibration.Data.rightJost_left_expansion` — chebyshev2, Lemma 11;
Right-filter bounds, endpoint conditions, ODE, Jost and integral formulas.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Sobolev chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `reflected` of type `ℝ → ℝ` by `fun x => m (-x)`.

Use: `chebyshev2.Filters.jostWronskian` uses this definition in the displayed construction
of `jostWronskian`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def reflected (m : ℝ → ℝ) : ℝ → ℝ := fun x => m (-x)

/--
Integrability of the displayed function: `Integrable (reflected m)`.

Use: `chebyshev2.Filters.jostWronskian_derivative` uses this integrability result to
establish the actual derivative at the stated point: `HasDerivAt (jostWronskian s m) 0 x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem reflected_integrable {m : ℝ → ℝ} (hm : Integrable m) : Integrable (reflected m) :=
  ((Measure.measurePreserving_neg volume).integrable_comp hm.aestronglyMeasurable).2 hm

/--
Establishes the uniform, quantified assertion `∀ x, 0 ≤ reflected m x`.

Use: `chebyshev2.Filters.jostWronskian_constant` uses this bound to establish exact
identity `jostWronskian s m x=jostWronskian s m 0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem reflected_nonneg {m : ℝ → ℝ} (hn : ∀ x, 0 ≤ m x) : ∀ x, 0 ≤ reflected m x :=
  fun x => hn (-x)

/--
Continuity of the displayed function: `Continuous (reflected m)`.

Use: `chebyshev2.Filters.jostWronskian_constant` uses this continuity result to establish
exact identity `jostWronskian s m x=jostWronskian s m 0`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem reflected_continuous {m : ℝ → ℝ} (hc : Continuous m) : Continuous (reflected m) :=
  hc.comp continuous_neg

variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : Continuous m)
variable {s : ℝ} (hs : 0 ≤ s)

/--
Defines `jostWronskian` of type `ℝ` by `(2+nonlinear s m x+nonlinear s (reflected m) (-x))*jost
s m x*jost s (reflected m) (-x)`.

Use: `chebyshev2.Filters.jostWronskian_constant` uses this definition to establish exact
identity `jostWronskian s m x=jostWronskian s m 0`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.
-/
def jostWronskian (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2+nonlinear s m x+nonlinear s (reflected m) (-x))*jost s m x*jost s (reflected m) (-x)
include hm hn hc hs

/--
The actual derivative at the stated point: `HasDerivAt (jostWronskian s m) 0 x`.

Use: `chebyshev2.Filters.jostWronskian_constant` uses this derivative formula to establish
exact identity `jostWronskian s m x=jostWronskian s m 0`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
`chebyshev2.Filters.reflected_nonneg`, `chebyshev2.Filters.reflected_continuous` with
the arguments shown in the proof.
-/
theorem jostWronskian_derivative (x : ℝ) : HasDerivAt (jostWronskian s m) 0 x := by
  -- Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.Filters.reflected_nonneg`, `chebyshev2.Filters.reflected_continuous`
  -- with the arguments shown in the proof.
  have hmr := reflected_integrable hm
  have hnr := reflected_nonneg hn
  have hcr := reflected_continuous hc
  have hr := (nonlinear_hasDerivAt hmr hnr hcr hs (-x)).comp x (hasDerivAt_neg x)
  have hv := (jost_hasDerivAt_filter hmr hnr hs (-x)).comp x (hasDerivAt_neg x)
  have h := (((hasDerivAt_const x (2:ℝ)).add (nonlinear_hasDerivAt hm hn hc hs x)).add hr).mul
    (jost_hasDerivAt_filter hm hn hs x) |>.mul hv
  convert h using 1
  · rfl
  · simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,reflected,neg_neg]
    ring

/--
Exact identity `jostWronskian s m x=jostWronskian s m 0`.

Use: `chebyshev2.Filters.transmission_reflection` uses this identity to establish exact
identity `transmission s (reflected m)=transmission s m`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_c1`,
`chebyshev2.Filters.reflected_integrable`, `chebyshev2.Filters.reflected_nonneg` with
the arguments shown in the proof.
-/
theorem jostWronskian_constant (x : ℝ) : jostWronskian s m x=jostWronskian s m 0 := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_c1`,
  -- `chebyshev2.Filters.reflected_integrable`, `chebyshev2.Filters.reflected_nonneg`
  -- with the arguments shown in the proof.
  have hC : ContDiff ℝ 1 (jostWronskian s m) := by
    unfold jostWronskian
    exact (((contDiff_const.add (nonlinear_c1 hm hn hc hs)).add
      ((nonlinear_c1 (reflected_integrable hm) (reflected_nonneg hn)
        (reflected_continuous hc) hs).comp contDiff_neg)).mul (jost_c1 hm hn hs)).mul
      ((jost_c1 (reflected_integrable hm) (reflected_nonneg hn) hs).comp contDiff_neg)
  have he := locallyAC_integral_eq_sub (fun a b => hC.contDiffOn.absolutelyContinuousOnInterval)
    (Eventually.of_forall (jostWronskian_derivative hm hn hc hs)) 0 x
  simp only [intervalIntegral.integral_zero] at he
  linarith

/--
Exact identity `transmission s (reflected m)=transmission s m`.

Use: `chebyshev2.Filters.logDeterminant_reflection` rewrites with this identity to
establish the precise assertion is `logDeterminant (kernelEigenvalue (reflected_integrable hm)
(reflected_nonneg hn)) s= logDeterminant (kernelEigenvalue hm hn) s`.

Article: chebyshev2, Lemma 11 via `chebyshev2.Calibration.Data.rightJost_left_expansion`.

Proof: Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
`chebyshev2.Filters.reflected_nonneg`, `chebyshev2.Filters.nonlinear_limits` with the
arguments shown in the proof.
-/
theorem transmission_reflection : transmission s (reflected m)=transmission s m := by
  -- Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.Filters.reflected_nonneg`, `chebyshev2.Filters.nonlinear_limits` with
  -- the arguments shown in the proof.
  have hmr := reflected_integrable hm
  have hnr := reflected_nonneg hn
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto (jostWronskian s m) atBot (𝓝 (2*transmission s (reflected m))) := by
    change Tendsto (fun x => (2+nonlinear s m x+nonlinear s (reflected m) (-x))*
      jost s m x*jost s (reflected m) (-x)) atBot _
    -- Record the convergence h with its source filter and target limit before taking limits in
    -- the subsequent identities/bounds.
    have h := ((((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)) atBot (𝓝 2)).add (nonlinear_limits hm hn hs).1).add
      ((nonlinear_limits hmr hnr hs).2.comp tendsto_neg_atBot_atTop)).mul
        (jost_left_limit hm hn hs)).mul
        ((jost_right_limit hmr hnr hs).comp tendsto_neg_atBot_atTop)
    simpa only [jostWronskian,Function.comp_def,zero_add,add_zero,mul_one] using h
  -- Record the convergence hr with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hr : Tendsto (jostWronskian s m) atTop (𝓝 (2*transmission s m)) := by
    change Tendsto (fun x => (2+nonlinear s m x+nonlinear s (reflected m) (-x))*
      jost s m x*jost s (reflected m) (-x)) atTop _
    -- Record the convergence h with its source filter and target limit before taking limits in
    -- the subsequent identities/bounds.
    have h := ((((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2)).add (nonlinear_limits hm hn hs).2).add
      ((nonlinear_limits hmr hnr hs).1.comp tendsto_neg_atTop_atBot)).mul
        (jost_right_limit hm hn hs)).mul
        ((jost_left_limit hmr hnr hs).comp tendsto_neg_atTop_atBot)
    simpa only [jostWronskian,Function.comp_def,zero_add,add_zero,mul_one] using h
  -- Record the convergence hcl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hcl : Tendsto (jostWronskian s m) atBot (𝓝 (jostWronskian s m 0)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall (fun x => (jostWronskian_constant hm hn hc hs x).symm))
  -- Record the convergence hcr with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hcr : Tendsto (jostWronskian s m) atTop (𝓝 (jostWronskian s m 0)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall (fun x => (jostWronskian_constant hm hn hc hs x).symm))
  linarith [tendsto_nhds_unique hl hcl,tendsto_nhds_unique hr hcr]

/--
The precise assertion is `logDeterminant (kernelEigenvalue (reflected_integrable hm)
(reflected_nonneg hn)) s= logDeterminant (kernelEigenvalue hm hn) s`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
`chebyshev2.Filters.reflected_nonneg`,
`chebyshev2.Filters.log_transmission_eq_logDeterminant` with the arguments shown in the
proof.
-/
theorem logDeterminant_reflection :
    logDeterminant (kernelEigenvalue (reflected_integrable hm) (reflected_nonneg hn)) s=
      logDeterminant (kernelEigenvalue hm hn) s := by
  rw [← log_transmission_eq_logDeterminant (reflected_integrable hm) (reflected_nonneg hn) hs,
    ← log_transmission_eq_logDeterminant hm hn hs,transmission_reflection hm hn hc hs]

end
end chebyshev2.Filters
