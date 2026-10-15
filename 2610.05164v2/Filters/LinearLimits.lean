import «2610.05164v2».Filters.Linear

/-!
Article: 2610.05164v2, Proposition 3.
Linear Limits.
Use: `«2610.05164v2».Filters.causal_integrable` feeds
`«2610.05164v2».Filters.causal_derivative_integrable` (causal derivative integrable).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun x => kernel
c x t) atBot (𝓝 0)`.

Use: `«2610.05164v2».Filters.causal_tendsto_atBot` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (causal c j) atBot (𝓝 0)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem kernel_tendsto_atBot (c t : ℝ) : Tendsto (fun x => kernel c x t) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot t] with x hx
  simp [kernel,not_le.mpr hx]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun x => kernel
c x t) atTop (𝓝 0)`.

Use: `«2610.05164v2».Filters.causal_tendsto_atTop` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (causal c j) atTop (𝓝 0)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem kernel_tendsto_atTop {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun x => kernel c x t) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x-t) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have he := tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hc) ht)
  apply he.congr'
  filter_upwards [eventually_ge_atTop t] with x hx
  simp only [Function.comp_apply,kernel,indicator_of_mem (show t ∈ Iic x from hx)]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (causal c j) l
(𝓝 0)`.

Use: `«2610.05164v2».Filters.causal_tendsto_atBot` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (causal c j) atBot (𝓝 0)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_integral`,
`«2610.05164v2».Filters.kernel_mul_integrable`, `«2610.05164v2».Filters.kernel_nonneg` with the
arguments shown in the proof. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
private theorem causal_limit {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ} (hj : Integrable j)
    (l : Filter ℝ) [l.IsCountablyGenerated]
    (hl : ∀ t, Tendsto (fun x => kernel c x t) l (𝓝 0)) : Tendsto (causal c j) l (𝓝 0) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  have he : causal c j = fun x => ∫ t, kernel c x t*j t := funext causal_integral
  rw [he]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (F := fun x t => kernel c x t*j t) (f := fun _ => (0:ℝ)) (fun t => ‖j t‖)
    (Eventually.of_forall (fun x => (kernel_mul_integrable hc hj x).aestronglyMeasurable))
    (Eventually.of_forall (fun x => Eventually.of_forall (fun t => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg c x t)]
      exact mul_le_of_le_one_left (norm_nonneg _) (kernel_le_one hc x t)))) hj.norm
    (Eventually.of_forall (fun t => by simpa only [zero_mul] using (hl t).mul_const (j t)))
  simpa only [integral_zero] using ht

/--
Convergence along the specified source filter to the specified limit: `Tendsto (causal c j)
atBot (𝓝 0)`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this limit to establish
exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».Filters.LinearLimits.0.«2610.05164v2».Filters.causal_limit`,
`«2610.05164v2».Filters.kernel_tendsto_atBot` with the arguments shown in the proof.
-/
theorem causal_tendsto_atBot {c : ℝ} (hc : 0 ≤ c) {j : ℝ → ℝ} (hj : Integrable j) :
    Tendsto (causal c j) atBot (𝓝 0) := causal_limit hc hj atBot (kernel_tendsto_atBot c)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (causal c j)
atTop (𝓝 0)`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this limit to establish
exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».Filters.LinearLimits.0.«2610.05164v2».Filters.causal_limit`,
`«2610.05164v2».Filters.kernel_tendsto_atTop` with the arguments shown in the proof.
-/
theorem causal_tendsto_atTop {c : ℝ} (hc : 0 < c) {j : ℝ → ℝ} (hj : Integrable j) :
    Tendsto (causal c j) atTop (𝓝 0) := causal_limit hc.le hj atTop (kernel_tendsto_atTop hc)

/--
Defines `impulse` of type `ℝ → ℝ` by `(Ici (0:ℝ)).indicator (fun x => exp (-c*x))`.

Use: `«2610.05164v2».Filters.causal_convolution` rewrites with this definition to establish
exact identity `causal c j = convolution j (impulse c) (ContinuousLinearMap.mul ℝ ℝ)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.
-/
def impulse (c : ℝ) : ℝ → ℝ := (Ici (0:ℝ)).indicator (fun x => exp (-c*x))

/--
Integrability of the displayed function: `Integrable (impulse c)`.

Use: `«2610.05164v2».Filters.causal_integrable` uses this integrability result to establish
integrability of the displayed function: `Integrable (causal c j)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem impulse_integrable {c : ℝ} (hc : 0 < c) : Integrable (impulse c) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  exact integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0

/--
Exact identity `(∫ x, impulse c x) = 1/c`.

Use: `«2610.05164v2».Filters.causal_mass` rewrites with this identity to establish exact
identity `(∫ x, causal c j x) = (∫ t, j t)/c`.

Article: 2610.05164v2, Proposition 3.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem impulse_mass {c : ℝ} (hc : 0 < c) : (∫ x, impulse c x) = 1/c := by
  rw [impulse,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hc)]
  simp

/--
Exact identity `causal c j = convolution j (impulse c) (ContinuousLinearMap.mul ℝ ℝ)`.

Use: `«2610.05164v2».Filters.causal_integrable` rewrites with this identity to establish
integrability of the displayed function: `Integrable (causal c j)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral. Prove equality of functions by evaluating both sides at an
arbitrary argument.
-/
theorem causal_convolution (c : ℝ) (j : ℝ → ℝ) :
    causal c j = convolution j (impulse c) (ContinuousLinearMap.mul ℝ ℝ) := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  funext x
  rw [causal_integral,convolution_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change kernel c x t*j t=j t*impulse c (x-t)
    by_cases ht : t ≤ x
    · rw [kernel,indicator_of_mem (show t ∈ Iic x from ht),impulse,
        indicator_of_mem (show x-t ∈ Ici (0:ℝ) from sub_nonneg.mpr ht)]
      ring
    · simp [kernel,impulse,ht,show ¬0 ≤ x-t by linarith])

/--
Integrability of the displayed function: `Integrable (causal c j)`.

Use: `«2610.05164v2».Filters.causal_derivative_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => j x-c*causal c j x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_convolution`,
`«2610.05164v2».Filters.impulse_integrable` with the arguments shown in the proof.
-/
theorem causal_integrable {c : ℝ} (hc : 0 < c) {j : ℝ → ℝ} (hj : Integrable j) :
    Integrable (causal c j) := by
  rw [causal_convolution]
  exact hj.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (impulse_integrable hc)

/--
Exact identity `(∫ x, causal c j x) = (∫ t, j t)/c`.

Use: `«2610.05164v2».Filters.causal_derivative_norm` rewrites with this identity to establish
the stated quantitative bound `(∫ x, ‖j x-c*causal c j x‖) ≤ 2*(∫ x, j x)`.

Article: 2610.05164v2, Proposition 3.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_convolution`,
`«2610.05164v2».Filters.impulse_integrable`, `«2610.05164v2».Filters.impulse_mass` with the
arguments shown in the proof.
-/
theorem causal_mass {c : ℝ} (hc : 0 < c) {j : ℝ → ℝ} (hj : Integrable j) :
    (∫ x, causal c j x) = (∫ t, j t)/c := by
  rw [causal_convolution,integral_convolution _ hj (impulse_integrable hc),impulse_mass hc]
  simp [div_eq_mul_inv]

/--
Integrability of the displayed function: `Integrable (fun x => j x-c*causal c j x)`.

Use: `«2610.05164v2».Filters.causal_derivative_norm` uses this integrability result to
establish the stated quantitative bound `(∫ x, ‖j x-c*causal c j x‖) ≤ 2*(∫ x, j x)`.

Article: 2610.05164v2, Proposition 3.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_integrable` with the
arguments shown in the proof.
-/
theorem causal_derivative_integrable {c : ℝ} (hc : 0 < c) {j : ℝ → ℝ} (hj : Integrable j) :
    Integrable (fun x => j x-c*causal c j x) := hj.sub ((causal_integrable hc hj).const_mul c)

/--
The stated quantitative bound `(∫ x, ‖j x-c*causal c j x‖) ≤ 2*(∫ x, j x)`.

Use: `«2610.05164v2».Filters.linear_derivative_L1` uses this bound to establish the stated
quantitative bound `(∫ x, ‖groundParameter hm hn*m x-2*linear hm hn x‖) ≤ 2*groundParameter hm
hn*(∫ x, m x)`.

Article: 2610.05164v2, Proposition 3.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem causal_derivative_norm {c : ℝ} (hc : 0 < c) {j : ℝ → ℝ}
    (hj : Integrable j) (hn : ∀ᵐ x, 0 ≤ j x) :
    (∫ x, ‖j x-c*causal c j x‖) ≤ 2*(∫ x, j x) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hi := causal_integrable hc hj
  calc
    _ ≤ (∫ x, ‖j x‖+c*causal c j x) := by
      apply integral_mono_ae (causal_derivative_integrable hc hj).norm (hj.norm.add (hi.const_mul c))
      exact hn.mono (fun x _ => by
        calc
          ‖j x-c*causal c j x‖ ≤ ‖j x‖+‖c*causal c j x‖ := norm_sub_le _ _
          _ = _ := by
            change ‖j x‖+‖c*causal c j x‖ = ‖j x‖+c*causal c j x
            congr 1
            exact abs_of_nonneg (mul_nonneg hc.le (causal_nonneg hn x)))
    _ = 2*(∫ x, j x) := by
      rw [integral_add hj.norm (hi.const_mul c),integral_const_mul,causal_mass hc hj]
      have he : (∫ x, ‖j x‖) = ∫ x, j x := integral_congr_ae
        (hn.mono (fun _ hx => by simp only [Real.norm_eq_abs,abs_of_nonneg hx]))
      rw [he,mul_div_cancel₀ _ hc.ne']
      ring

end
end «2610.05164v2».Filters
