import chebyshev2.Filters.Nonlinear

/-!
Article: chebyshev2, Proposition 3.
The analytic transmission identity.
Use: `chebyshev2.Filters.nonlinear_mass` feeds `chebyshev2.Filters.nonlinear_derivative_L1`
(Proposition 3(ii)'s derivative bound for any uniform bound B on the filter).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.GroundState chebyshev2.Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `transmission` of type `ℝ` by `1+s/2*∫ t, m t*jost s m t`.

Use: `chebyshev2.Filters.jost_right_limit` uses this definition to establish convergence
along the specified source filter to the specified limit: `Tendsto (jost s m) atTop (𝓝
(transmission s m))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.
-/
def transmission (s : ℝ) (m : ℝ → ℝ) : ℝ := 1+s/2*∫ t, m t*jost s m t

/--
The stated quantitative bound `1 ≤ transmission s m`.

Use: `chebyshev2.Filters.nonlinear_mass` uses this bound to establish the identity `(∫ t,
nonlinear s m t)=log (transmission s m)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_positive` with the arguments
shown in the proof.
-/
theorem transmission_ge_one {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : 1 ≤ transmission s m := by
  have hi : 0 ≤ ∫ t, m t*jost s m t := integral_nonneg
    (fun t => mul_nonneg (hn t) (jost_positive hm hn hs t).le)
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hs (by norm_num : (0:ℝ) ≤ 2)) hi)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (jost s m) atTop
(𝓝 (transmission s m))`.

Use: `chebyshev2.Filters.nonlinear_mass` uses this limit to establish the identity `(∫ t,
nonlinear s m t)=log (transmission s m)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem jost_right_limit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (jost s m) atTop (𝓝 (transmission s m)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hj := jost_forcing_integrable hm hn hs
  have h := ((cumulative_right_limit hj).sub
    (causal_tendsto_atTop (by norm_num : (0:ℝ) < 2) hj)).const_mul (s/2) |>.const_add 1
  change Tendsto (fun x => 1+s/2*(cumulative (fun t => m t*jost s m t) x-
    causal 2 (fun t => m t*jost s m t) x)) atTop (𝓝 (1+s/2*((∫ t, m t*jost s m t)-0))) at h
  have he : (fun x => 1+volterra s m (jost s m) x)=jost s m :=
    funext (fun x => (jost_equation hm hn hs x).symm)
  change Tendsto (fun x => 1+volterra s m (jost s m) x) atTop _ at h
  simpa only [transmission,he,sub_zero] using h

/--
The actual derivative at the stated point: `HasDerivAt (fun x => log (jost s m x)) (nonlinear s
m x) x`.

Use: `chebyshev2.Filters.log_jost_integral` uses this derivative formula to establish exact
identity `(∫ t in Iic x, nonlinear s m t)=log (jost s m x)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_positive`,
`chebyshev2.Filters.jost_hasDerivAt` with the arguments shown in the proof.
-/
theorem log_jost_hasDerivAt {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    HasDerivAt (fun x => log (jost s m x)) (nonlinear s m x) x := by
  convert (Real.hasDerivAt_log (jost_positive hm hn hs x).ne').comp x (jost_hasDerivAt hm hn hs x) using 1
  · rfl
  · dsimp only [nonlinear]
    ring

/--
The logarithm of the actual Jost solution is the primitive of its filter.

Exact identity `(∫ t in Iic x, nonlinear s m t)=log (jost s m x)`.

Use: `chebyshev2.Filters.jost_exp_primitive` rewrites with this identity to establish exact
identity `jost s m x=exp (∫ t in Iic x, nonlinear s m t)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.locallyAC_integral_Iic`,
`chebyshev2.Filters.jost_c1`, `chebyshev2.Filters.jost_positive` with the arguments
shown in the proof.
-/
theorem log_jost_integral {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : (∫ t in Iic x, nonlinear s m t)=log (jost s m x) := by
  -- Use the identities/estimates `chebyshev2.Filters.locallyAC_integral_Iic`,
  -- `chebyshev2.Filters.jost_c1`, `chebyshev2.Filters.jost_positive` with the
  -- arguments shown in the proof.
  apply locallyAC_integral_Iic
  · intro a b
    exact ((jost_c1 hm hn hs).log (fun x => (jost_positive hm hn hs x).ne')).contDiffOn.absolutelyContinuousOnInterval
  · exact Eventually.of_forall (log_jost_hasDerivAt hm hn hs)
  · exact nonlinear_integrable hm hn hs
  · simpa only [Function.comp_def,log_one] using (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp
      (jost_left_limit hm hn hs)

/--
Exact identity `jost s m x=exp (∫ t in Iic x, nonlinear s m t)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates `chebyshev2.Filters.log_jost_integral`,
`chebyshev2.Filters.jost_positive` with the arguments shown in the proof.
-/
theorem jost_exp_primitive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : jost s m x=exp (∫ t in Iic x, nonlinear s m t) := by rw [log_jost_integral hm hn hs,exp_log (jost_positive hm hn hs x)]

/--
The analytic transmission identity. Its identification with the spectral Fredholm determinant
is deliberately a separate theorem.

Exact identity `(∫ t, nonlinear s m t)=log (transmission s m)`.

Use: `chebyshev2.Filters.nonlinear_derivative_L1` rewrites with this identity to establish
the stated quantitative bound `(∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤ s*(∫ x, m
x)+(2+B)*log (transmission s m)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem nonlinear_mass {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : (∫ t, nonlinear s m t)=log (transmission s m) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hleft := log_jost_integral hm hn hs (0:ℝ)
  -- Record the convergence hlog with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlog : Tendsto (fun x => log (jost s m x)) atTop (𝓝 (log (transmission s m))) :=
    (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans_le (transmission_ge_one hm hn hs)))).tendsto.comp
      (jost_right_limit hm hn hs)
  have he : (fun x => ∫ t in (0:ℝ)..x, nonlinear s m t)=
      fun x => log (jost s m x)-log (jost s m 0) := by
    funext x
    exact locallyAC_integral_eq_sub (fun a b =>
      ((jost_c1 hm hn hs).log (fun t => (jost_positive hm hn hs t).ne')).contDiffOn.absolutelyContinuousOnInterval)
      (Eventually.of_forall (log_jost_hasDerivAt hm hn hs)) 0 x
  have hlim := intervalIntegral_tendsto_integral_Ioi (0:ℝ) (nonlinear_integrable hm hn hs).integrableOn tendsto_id
  change Tendsto (fun x : ℝ => ∫ t in (0:ℝ)..x, nonlinear s m t) atTop _ at hlim
  rw [he] at hlim
  have hright := tendsto_nhds_unique hlim (hlog.sub_const (log (jost s m 0)))
  rw [← intervalIntegral.integral_Iic_add_Ioi (nonlinear_integrable hm hn hs).integrableOn
    (nonlinear_integrable hm hn hs).integrableOn (b := 0),hleft,hright]
  ring

end
end chebyshev2.Filters
