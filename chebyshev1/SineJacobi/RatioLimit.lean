import chebyshev1.SineJacobi.LogRatio
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Article: chebyshev1, Theorem E.3.
The bulk ratio asymptotic, with arbitrary moving sites and arbitrary index filters.
Use: `chebyshev1.SineJacobi.ratio_scaled_limit` feeds
`chebyshev1.SineJacobi.convolutionStep_limit` (convolution Step limit).
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set Filter Topology

/--
Convergence along the specified source filter to the specified limit: `Tendsto k l atTop`.

Use: `chebyshev1.SineJacobi.ratio_scaled_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun a => sqrt (N a:ℝ)*ratio
(N a) (k a)) l (𝓝 (1/sqrt (sin (Real.pi*t))))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem mesh_index_atTop {α : Type*} {l : Filter α} {N k : α → ℕ} {t : ℝ}
    (hN : Tendsto N l atTop) (ht : 0 < t)
    (hk : Tendsto (fun a => (k a:ℝ)/(N a:ℝ)) l (𝓝 t)) : Tendsto k l atTop := by
  -- Record the convergence hNr with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hNr : Tendsto (fun a => (N a:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hN
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply tendsto_atTop_mono' l _ (hNr.const_mul_atTop (half_pos ht))
  filter_upwards [hk.eventually_const_lt (by linarith : t/2 < t),
    hNr.eventually_gt_atTop 0] with a ha hna
  exact le_of_lt ((lt_div_iff₀ hna).mp ha)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
logRatio (N a) (k a)+logSinc ((k a:ℝ)/(N a:ℝ))/2) l (𝓝 0)`.

Use: `chebyshev1.SineJacobi.ratio_over_binomial_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a => ratio
(N a) (k a)/binomialRatio (k a)) l (𝓝 (1/sqrt (sinc (Real.pi*t))))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem logRatio_correction_limit {α : Type*} {l : Filter α} {N k : α → ℕ} {t : ℝ}
    (hN : Tendsto N l atTop) (ht : t ∈ Ioo (0:ℝ) 1)
    (hk : Tendsto (fun a => (k a:ℝ)/(N a:ℝ)) l (𝓝 t)) :
    Tendsto (fun a => logRatio (N a) (k a)+logSinc ((k a:ℝ)/(N a:ℝ))/2) l (𝓝 0) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  let b := (t+1)/2
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hb0 : 0 ≤ b := by dsimp [b]; linarith [ht.1]
  have hb1 : b < 1 := by dsimp [b]; linarith [ht.2]
  obtain ⟨M, hM, hbnd⟩ := logSinc_second_bound hb0 hb1
  have h1 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ) |>.comp hN
  -- Record the convergence hboundlim with its source filter and target limit before taking
  -- limits in the subsequent identities/bounds.
  have hboundlim : Tendsto (fun a => M/(N a:ℝ)) l (𝓝 0) := by
    simpa only [mul_zero, mul_one_div, Function.comp_def] using (tendsto_const_nhds (x := M)).mul h1
  apply squeeze_zero_norm' _ hboundlim
  filter_upwards [hk.eventually_lt_const htb, hN.eventually_gt_atTop 0] with a ha hna
  have hNr : 0 < (N a:ℝ) := by exact_mod_cast hna
  have hkN : k a < N a := by
    have hlt : (k a:ℝ)/(N a:ℝ) < 1 := ha.trans hb1
    rw [div_lt_one hNr] at hlt
    exact_mod_cast hlt
  have h := logRatio_error_bound hb0 hb1 hM hbnd (N a) (k a) hkN ha.le
  have hle : (k a:ℝ) ≤ N a := by exact_mod_cast hkN.le
  have he : M*(N a:ℝ)/(N a:ℝ)^2 = M/(N a:ℝ) := by field_simp [hNr.ne']
  rw [Real.norm_eq_abs]
  exact h.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hM)
    (sq_nonneg _)).trans_eq he)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun a => ratio
(N a) (k a)/binomialRatio (k a)) l (𝓝 (1/sqrt (sinc (Real.pi*t))))`.

Use: `chebyshev1.SineJacobi.ratio_scaled_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun a => sqrt (N a:ℝ)*ratio
(N a) (k a)) l (𝓝 (1/sqrt (sin (Real.pi*t))))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem ratio_over_binomial_limit {α : Type*} {l : Filter α} {N k : α → ℕ} {t : ℝ}
    (hN : Tendsto N l atTop) (ht : t ∈ Ioo (0:ℝ) 1)
    (hk : Tendsto (fun a => (k a:ℝ)/(N a:ℝ)) l (𝓝 t)) :
    Tendsto (fun a => ratio (N a) (k a)/binomialRatio (k a)) l
      (𝓝 (1/sqrt (sinc (Real.pi*t)))) := by
  -- Record the convergence hg with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hg : Tendsto (fun a => logSinc ((k a:ℝ)/(N a:ℝ))) l (𝓝 (logSinc t)) :=
    ((logSinc_contDiff.continuousOn t ⟨by linarith [ht.1], ht.2⟩).continuousAt
      (isOpen_Ioo.mem_nhds ⟨by linarith [ht.1], ht.2⟩)).tendsto.comp hk
  have he := (logRatio_correction_limit hN ht hk).sub (hg.div_const 2)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp he
  have hs := sinc_pi_pos (x := t) ⟨by linarith [ht.1], ht.2⟩
  have hv : exp (0-logSinc t/2) = 1/sqrt (sinc (Real.pi*t)) := by
    rw [zero_sub, logSinc, ← log_sqrt hs.le, exp_neg, exp_log (sqrt_pos.mpr hs)]
    simp only [one_div]
  rw [hv] at hexp
  apply hexp.congr'
  filter_upwards [hk.eventually_lt_const ht.2, hN.eventually_gt_atTop 0] with a ha hna
  have hNr : 0 < (N a:ℝ) := by exact_mod_cast hna
  have hkN : k a < N a := by exact_mod_cast (div_lt_one hNr).mp ha
  simp only [add_sub_cancel_right, logRatio]
  exact exp_log (div_pos (ratio_pos (N a) (k a) hkN) (binomialRatio_pos _))

/--
The bulk ratio asymptotic, with arbitrary moving sites and arbitrary index filters.

Convergence along the specified source filter to the specified limit: `Tendsto (fun a => sqrt
(N a:ℝ)*ratio (N a) (k a)) l (𝓝 (1/sqrt (sin (Real.pi*t))))`.

Use: `chebyshev1.SineJacobi.convolutionStep_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun a => convolutionStep (N
a) (s a) x) l (𝓝 (convolutionKernel t x))`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem ratio_scaled_limit {α : Type*} {l : Filter α} {N k : α → ℕ} {t : ℝ}
    (hN : Tendsto N l atTop) (ht : t ∈ Ioo (0:ℝ) 1)
    (hk : Tendsto (fun a => (k a:ℝ)/(N a:ℝ)) l (𝓝 t)) :
    Tendsto (fun a => sqrt (N a:ℝ)*ratio (N a) (k a)) l
      (𝓝 (1/sqrt (sin (Real.pi*t)))) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hka := mesh_index_atTop hN ht.1 hk
  have hb := binomialRatio_scaled_limit.comp hka
  have hr := ratio_over_binomial_limit hN ht hk
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := Real.pi)).mul hk)
  have hpt : 0 < Real.pi*t := mul_pos pi_pos ht.1
  have hh := (hb.mul hr).div hs (sqrt_pos.mpr hpt).ne'
  have hsin : sin (Real.pi*t) = Real.pi*t*sinc (Real.pi*t) := by
    rw [sinc_of_ne_zero hpt.ne']; field_simp [ht.1.ne']
  have hv : 1*(1/sqrt (sinc (Real.pi*t)))/sqrt (Real.pi*t) =
      1/sqrt (sin (Real.pi*t)) := by
    rw [hsin, sqrt_mul hpt.le]
    ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_gt_atTop 0, hka.eventually_gt_atTop 0] with a hna hka
  have hNr : 0 < (N a:ℝ) := by exact_mod_cast hna
  have hkr : 0 < (k a:ℝ) := by exact_mod_cast hka
  have hn0 := (sqrt_pos.mpr hNr).ne'
  have hk0 := (sqrt_pos.mpr (mul_pos pi_pos hkr)).ne'
  have he : sqrt (Real.pi*((k a:ℝ)/(N a:ℝ))) =
      sqrt (Real.pi*(k a:ℝ))/sqrt (N a:ℝ) := by
    rw [← mul_div_assoc, sqrt_div (mul_pos pi_pos hkr).le]
  change (binomialRatio (k a)*sqrt (Real.pi*(k a:ℝ)))*
    (ratio (N a) (k a)/binomialRatio (k a))/sqrt (Real.pi*((k a:ℝ)/(N a:ℝ))) = _
  rw [he]
  field_simp [hn0, hk0, (binomialRatio_pos (k a)).ne']


end
end chebyshev1.SineJacobi
