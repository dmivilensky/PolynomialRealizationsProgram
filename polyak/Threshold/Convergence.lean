import polyak.Threshold.Upper
import polyak.Growth.Original
import polyak.Functions.Minimizer

/-!
Article: Theorem threshold, convergence of every genuine subcritical trajectory.
Use: actual heavy-ball iterates converge in arbitrary complete real Hilbert spaces,
not merely in a spectral model or one fixed finite dimension.
Proof: normalize the source run, bound every finite segment by Γ, and choose
a strict geometric majorant whose ratio is below one.
-/

noncomputable section

open Filter
open scoped Topology

namespace polyak.Threshold

open Dynamics Growth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: the dimension-independent finite-horizon bound also holds in an arbitrary Hilbert space. -/
theorem original_norm_le_envelope {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a : E) (hmin : ∀ y, f a ≤ f y)
    (α β : ℝ) (x₀ : E) (N : ℕ) :
    ‖iterate (gradient f) α β x₀ N-a‖ ≤
      Real.sqrt 2*envelope (normalizedA μ L α β) (normalizedB μ L α) β N*‖x₀-a‖ := by
  let ψ := originalPotential μ L f a
  let A := normalizedA μ L α β
  let B := normalizedB μ L α
  let x := restPosition (gradient ψ) A B β (x₀-a)
  have hψ : NormalizedSmooth ψ := originalPotential_normalized hf a hmin
  let s := Segment.ofNormalized hψ x N (fun k _ => restPosition_recurrence _ _ _ _ _ k)
  have hs := stateNorm_le_envelope_hilbert s
  have hs0 : stateNorm x 0 = Real.sqrt 2*‖x₀-a‖ := restPosition_stateNorm_zero _ _ _ _ _
  have he : x (N+1) = iterate (gradient f) α β x₀ N-a := by
    have hh := (original_normalized_run hf a hmin α β x₀).2 N
    exact (congrArg Prod.fst hh).symm
  have hb := norm_right_le_stateNorm x N
  rw [he] at hb
  calc
    _ ≤ stateNorm x N := hb
    _ ≤ envelope A B β N*stateNorm x 0 := hs
    _ = _ := by rw [hs0]; ring

/-- Article: the method converges on every source objective below the exact threshold.
Use: no regularity beyond the original differentiability and Lipschitz gradient is imposed. -/
theorem polyak_converges {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a : E) (hmin : ∀ y, f a ≤ f y)
    (hc : polyakQ μ L < criticalQ) (x₀ : E) :
    Tendsto (iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀) atTop (𝓝 a) := by
  have hμ := hf.mu_pos
  have hL := hf.mu_lt_L
  let q := polyakQ μ L
  let r := polyakGrowthRate q
  let R := (r+1)/2
  have hrpos : 0 < r := growthRate_pos _ _ _
  have hr1 : r < 1 := polyakGrowthRate_lt_one (polyakQ_pos hμ hL) hc
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hrR : growthRate 0 (2*q) (q^2) < R := by change r < R; dsimp [R]; linarith
  have hq : 0 < q := polyakQ_pos hμ hL
  obtain ⟨C,hC,hΓ⟩ := exists_envelope_le_mul_pow
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hq.ne') hrR
  have hbound (N : ℕ) : ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N-a‖ ≤
      (Real.sqrt 2*C*‖x₀-a‖)*R^N := by
    have hn := original_norm_le_envelope hf a hmin (polyakAlpha μ L) (polyakBeta μ L) x₀ N
    rw [polyak_normalizedA hμ hL,polyak_normalizedB hμ hL] at hn
    change ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N-a‖ ≤
      Real.sqrt 2*envelope 0 (2*q) (q^2) N*‖x₀-a‖ at hn
    have hm := mul_le_mul_of_nonneg_left (hΓ N) (Real.sqrt_nonneg 2)
    have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg (x₀-a))
    exact hn.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hm')
  have hlim : Tendsto (fun N : ℕ => (Real.sqrt 2*C*‖x₀-a‖)*R^N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hRpos.le hR1).const_mul (Real.sqrt 2*C*‖x₀-a‖)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)

/-- Article: the threshold comparison can be stated directly in the original condition number. -/
theorem polyak_converges_of_condition {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a : E) (hmin : ∀ y, f a ≤ f y)
    (hc : L/μ < criticalKappa) (x₀ : E) :
    Tendsto (iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀) atTop (𝓝 a) := by
  have hκ : 1 < L/μ := (one_lt_div hf.mu_pos).mpr hf.mu_lt_L
  apply polyak_converges hf a hmin _ x₀
  rw [polyakQ_eq_conditionQ hf.mu_pos hf.mu_lt_L]
  exact (conditionQ_lt_critical_iff hκ).mpr hc

end polyak.Threshold
