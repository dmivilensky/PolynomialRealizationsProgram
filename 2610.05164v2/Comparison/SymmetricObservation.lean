import «2610.05164v2».Filters.ReflectionObservation

/-!
Article: 2610.05164v2, Theorem 5.1.
Lemma 14's determinant formula at the symmetry center.
Use: `«2610.05164v2».Comparison.symmetric_logDeterminant` feeds
`«2610.05164v2».Primal.determinant_cubic` (determinant cubic).
Proof chain: `«2610.05164v2».Primal.determinant_cubic` — 2610.05164v2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
-/
namespace «2610.05164v2».Comparison
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Filters «2610.05164v2».GroundState «2610.05164v2».Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : Continuous m)
variable {s : ℝ} (hs : 0 ≤ s)
include hm hn hc hs

/--
Exact identity `jostWronskian s m x=2*transmission s m`.

Use: `«2610.05164v2».Comparison.symmetric_transmission` uses this identity to establish exact
identity `transmission s m=(1+nonlinear s m 0)*(jost s m 0)^2`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_limits`,
`«2610.05164v2».Filters.reflected_integrable`, `«2610.05164v2».Filters.reflected_nonneg` with
the arguments shown in the proof.
-/
theorem jostWronskian_value (x : ℝ) : jostWronskian s m x=2*transmission s m := by
  -- Record the convergence hr with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hr : Tendsto (jostWronskian s m) atTop (𝓝 (2*transmission s m)) := by
    change Tendsto (fun x => (2+nonlinear s m x+nonlinear s (reflected m) (-x))*
      jost s m x*jost s (reflected m) (-x)) atTop _
    -- Record the convergence h with its source filter and target limit before taking limits in
    -- the subsequent identities/bounds.
    have h := ((((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2)).add
      (nonlinear_limits hm hn hs).2).add
      ((nonlinear_limits (reflected_integrable hm) (reflected_nonneg hn) hs).1.comp
        tendsto_neg_atTop_atBot)).mul (jost_right_limit hm hn hs)).mul
        ((jost_left_limit (reflected_integrable hm) (reflected_nonneg hn) hs).comp tendsto_neg_atTop_atBot)
    simpa only [Function.comp_def,add_zero,mul_one] using h
  -- Record the convergence hconst with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hconst : Tendsto (jostWronskian s m) atTop (𝓝 (jostWronskian s m 0)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall (fun x => (jostWronskian_constant hm hn hc hs x).symm))
  exact (jostWronskian_constant hm hn hc hs x).trans (tendsto_nhds_unique hconst hr)

/--
Exact identity `transmission s m=(1+nonlinear s m 0)*(jost s m 0)^2`.

Use: `«2610.05164v2».Comparison.symmetric_logDeterminant` rewrites with this identity to
establish the precise assertion is `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in Iic
(0:ℝ), nonlinear s m x)+log (1+nonlinear s m 0)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem symmetric_transmission (hSym : ∀ x, m (-x)=m x) :
    transmission s m=(1+nonlinear s m 0)*(jost s m 0)^2 := by
  have he : reflected m=m := funext hSym
  have h := jostWronskian_value hm hn hc hs 0
  simp only [jostWronskian,neg_zero,he] at h
  nlinarith

/--
The half-line integral includes the exact left tail; for compact densities it is the
support-to-center integral printed in Lemma 14.

The precise assertion is `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in Iic (0:ℝ),
nonlinear s m x)+log (1+nonlinear s m 0)`.

Use: `«2610.05164v2».Comparison.symmetric_logDeterminant_at` uses this identity to establish
the precise assertion is `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in Iic c, nonlinear
s m x)+log (1+nonlinear s m c)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates
`«2610.05164v2».Filters.log_transmission_eq_logDeterminant`,
`«2610.05164v2».Comparison.symmetric_transmission`, `«2610.05164v2».Filters.nonlinear_bounds`
with the arguments shown in the proof.
-/
theorem symmetric_logDeterminant (hSym : ∀ x, m (-x)=m x) :
    logDeterminant (kernelEigenvalue hm hn) s=
      2*(∫ x in Iic (0:ℝ), nonlinear s m x)+log (1+nonlinear s m 0) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.log_transmission_eq_logDeterminant`,
  -- `«2610.05164v2».Comparison.symmetric_transmission`,
  -- `«2610.05164v2».Filters.nonlinear_bounds` with the arguments shown in the proof.
  rw [← log_transmission_eq_logDeterminant hm hn hs,symmetric_transmission hm hn hc hs hSym,
    log_mul (by linarith [(nonlinear_bounds hm hn hs 0).1])
      (pow_ne_zero 2 (jost_positive hm hn hs 0).ne'),log_pow,log_jost_integral hm hn hs]
  ring

end
end «2610.05164v2».Comparison
