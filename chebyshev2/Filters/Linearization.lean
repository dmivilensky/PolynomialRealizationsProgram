import chebyshev2.Filters.Nonlinear

/-!
Article: chebyshev2, Proposition 3.
Proposition 3(ii): pointwise linearization from positive scales.
Use: `chebyshev2.Filters.nonlinear_linearization` feeds
`chebyshev2.Filters.nonlinear_ground_linearization` (nonlinear ground linearization).
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `s*causal 2 m x/exp (s*(∫ t, m t)/2) ≤ nonlinear s m x`.

Use: `chebyshev2.Filters.nonlinear_linearization` uses this bound to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun s => nonlinear s m x/s)
(𝓝[>] (0:ℝ)) (𝓝 (causal 2 m x))`.

Article: chebyshev2, Proposition 3 via `chebyshev2.Filters.nonlinear_linearization`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_integral`,
`chebyshev2.Filters.kernel_mul_integrable`,
`chebyshev2.Filters.jost_forcing_integrable` with the arguments shown in the proof.
-/
theorem nonlinear_lower_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    s*causal 2 m x/exp (s*(∫ t, m t)/2) ≤ nonlinear s m x := by
  -- Use the identities/estimates `chebyshev2.Filters.causal_integral`,
  -- `chebyshev2.Filters.kernel_mul_integrable`,
  -- `chebyshev2.Filters.jost_forcing_integrable` with the arguments shown in the proof.
  have hi : causal 2 m x ≤ causal 2 (fun t => m t*jost s m t) x := by
    rw [causal_integral, causal_integral]
    apply integral_mono (kernel_mul_integrable (by norm_num : (0:ℝ) ≤ 2) hm x)
      (kernel_mul_integrable (by norm_num : (0:ℝ) ≤ 2) (jost_forcing_integrable hm hn hs) x)
    intro t
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_right (hn t) (jost_bounds hm hn hs t).1) (kernel_nonneg 2 x t)
  calc
    _ ≤ s*causal 2 m x/jost s m x :=
      div_le_div_of_nonneg_left
        (mul_nonneg hs (causal_nonneg (Eventually.of_forall hn) x))
        (jost_positive hm hn hs x) (jost_uniform_bound hm hn hs x)
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi hs)
      (jost_positive hm hn hs x).le

/--
Proposition 3(ii): pointwise linearization from positive scales.

Convergence along the specified source filter to the specified limit: `Tendsto (fun s =>
nonlinear s m x/s) (𝓝[>] (0:ℝ)) (𝓝 (causal 2 m x))`.

Use: `chebyshev2.Filters.nonlinear_ground_linearization` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun s =>
groundParameter hm hn*nonlinear s m x/s) (𝓝[>] (0:ℝ)) (𝓝 (linear hm hn x))`.

Article: chebyshev2, Proposition 3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem nonlinear_linearization {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) : Tendsto (fun s => nonlinear s m x/s) (𝓝[>] (0:ℝ)) (𝓝 (causal 2 m x)) := by
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto (fun s : ℝ => causal 2 m x/exp (s*(∫ t, m t)/2))
      (𝓝[>] (0:ℝ)) (𝓝 (causal 2 m x)) := by
    -- Establish continuity hc before using the function at limits or in calculus arguments.
    have hc : Continuous (fun s : ℝ => causal 2 m x/exp (s*(∫ t, m t)/2)) :=
      continuous_const.div (by fun_prop) (fun _ => exp_ne_zero _)
    simpa only [zero_mul, zero_div, exp_zero, div_one] using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hsp : 0 < s := hs
    have h := (div_le_div_iff_of_pos_right hsp).mpr (nonlinear_lower_bound hm hn hsp.le x)
    convert h using 1
    field_simp
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hsp : 0 < s := hs
    apply (div_le_iff₀ hsp).mpr
    simpa only [mul_comm] using (nonlinear_bounds hm hn hsp.le x).2

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun s =>
groundParameter hm hn*nonlinear s m x/s) (𝓝[>] (0:ℝ)) (𝓝 (linear hm hn x))`.

Use: a standalone supporting limit for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_linearization` with the
arguments shown in the proof.
-/
theorem nonlinear_ground_linearization {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) : Tendsto (fun s => groundParameter hm hn*nonlinear s m x/s)
      (𝓝[>] (0:ℝ)) (𝓝 (linear hm hn x)) := by
  simpa only [linear, mul_div_assoc] using (nonlinear_linearization hm hn x).const_mul (groundParameter hm hn)

end
end chebyshev2.Filters
