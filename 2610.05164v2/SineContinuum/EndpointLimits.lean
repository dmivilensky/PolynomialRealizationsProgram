import «2610.05164v2».SineContinuum.EndpointBounds

/-!
Article: 2610.05164v2, Lemma 5.
The logarithmic zero-energy branch also vanishes at the endpoint.
Use: `«2610.05164v2».SineContinuum.r_left_limit` feeds `«2610.05164v2».SineContinuum.r_continuousOn`
(r continuous On).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Convergence along the specified source filter to the specified limit: `Tendsto l (𝓝[>] (0:ℝ))
(𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.l_continuousOn` uses this limit to establish continuity on
the stated domain: `ContinuousOn l (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem l_left_limit : Tendsto l (𝓝[>] (0:ℝ)) (𝓝 0) := by
  -- Record the convergence h0 with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- Record the convergence hs with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hs : Tendsto sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [sqrt_zero,Function.comp_def] using continuous_sqrt.continuousAt.tendsto.comp h0
  have h := l_boundary.mul hs
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_mul_cancel₀ _ (sqrt_pos.mpr ht).ne'

/--
Convergence along the specified source filter to the specified limit: `Tendsto ratio (𝓝[>]
(0:ℝ)) atTop`.

Use: `«2610.05164v2».SineContinuum.X_left_limit` uses this limit to establish convergence along
the specified source filter to the specified limit: `Tendsto X (𝓝[>] (0:ℝ)) atBot`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem ratio_left_limit : Tendsto ratio (𝓝[>] (0:ℝ)) atTop := by
  obtain ⟨b,hb,hbound⟩ := exists_endpoint_bounds
  have hlog := tendsto_log_nhdsGT_zero.const_mul_atBot (one_div_pos.mpr pi_pos)
  have hn := tendsto_neg_atBot_atTop.comp hlog
  have hlim := tendsto_atTop_add_const_left _ (correctedRatio (1/π) b) hn
  apply tendsto_atTop_mono' _ _ (by simpa only [sub_eq_add_neg] using hlim)
  filter_upwards [Ioo_mem_nhdsGT hb.1] with t ht
  exact (ratio_log_bounds hb hbound t ⟨ht.1,ht.2.le⟩).1

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun t => sqrt
t*log t) (𝓝[>] (0:ℝ)) (𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.r_left_limit` uses this limit to establish convergence along
the specified source filter to the specified limit: `Tendsto r (𝓝[>] (0:ℝ)) (𝓝 0)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sqrt_log_left_limit : Tendsto (fun t => sqrt t*log t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ)<1/2)
  simpa only [sqrt_eq_rpow,mul_comm] using h

/--
The logarithmic zero-energy branch also vanishes at the endpoint. The proof derives a
logarithmic bound from W=2 and the no-logarithm normalization, rather than importing a
special-function asymptotic.

Convergence along the specified source filter to the specified limit: `Tendsto r (𝓝[>] (0:ℝ))
(𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.l_right_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto l (𝓝[<] (1:ℝ)) (𝓝 0)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem r_left_limit : Tendsto r (𝓝[>] (0:ℝ)) (𝓝 0) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  obtain ⟨b,hb,hbound⟩ := exists_endpoint_bounds
  let C := correctedRatio (4/π) b
  -- Record the convergence h0 with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- Record the convergence hs with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hs : Tendsto sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [sqrt_zero,Function.comp_def] using continuous_sqrt.continuousAt.tendsto.comp h0
  -- Record the convergence hlim with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlim : Tendsto (fun t => sqrt (2*π)*(C*sqrt t-(4/π)*(sqrt t*log t)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x := sqrt (2*π))).mul ((hs.const_mul C).sub (sqrt_log_left_limit.const_mul (4/π)))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    exact (r_positive ht).le
  · filter_upwards [Ioo_mem_nhdsGT hb.1] with t ht
    have hi : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1,ht.2.trans hb.2⟩
    have hp := l_positive hi
    have hu := (ratio_log_bounds hb hbound t ⟨ht.1,ht.2.le⟩).2
    have hU : 0 ≤ C-(4/π)*log t := (div_pos (r_positive hi) hp).le.trans hu
    have hl : l t ≤ sqrt (2*π)*sqrt t := by
      have hsq : (sqrt (2*π)*sqrt t)^2=2*π*t := by
        rw [mul_pow,sq_sqrt (by positivity : 0 ≤ 2*π),sq_sqrt ht.1.le]
      have hn : 0 ≤ sqrt (2*π)*sqrt t := by positivity
      nlinarith [(hbound t ⟨ht.1,ht.2.le⟩).2]
    calc
      r t=l t*ratio t := by dsimp [ratio]; field_simp
      _ ≤ l t*(C-(4/π)*log t) := mul_le_mul_of_nonneg_left hu hp.le
      _ ≤ (sqrt (2*π)*sqrt t)*(C-(4/π)*log t) := mul_le_mul_of_nonneg_right hl hU
      _ = sqrt (2*π)*(C*sqrt t-(4/π)*(sqrt t*log t)) := by ring

end
end «2610.05164v2».SineContinuum
