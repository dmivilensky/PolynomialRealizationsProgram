import polyak.Threshold.Lower

/-!
Article: Theorem threshold, actual nonsubcritical examples.
Use: one three-dimensional objective and one from-rest start yield nonconvergence
at criticality and exponential divergence above it, on every time horizon.
Proof: the already realized fixed spiral example has factor at least one, or greater than one.
-/

noncomputable section

open Filter
open scoped Topology

namespace polyak.Threshold

open Dynamics

/-- Article: an actual three-dimensional counterexample at or above the threshold.
Use: nonconvergence refers to the true gradient iteration, with its prescribed start from rest. -/
theorem exists_nonconvergent_example {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : criticalQ ≤ polyakQ μ L) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, x₀ ≠ 0 ∧
        ¬ Tendsto (iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀) atTop (𝓝 0) := by
  obtain ⟨f,hf,x₀,hx,c₀,hc₀,hbound⟩ := exists_spiral_example hμ hL
  have hfac : 1 ≤ Spiral.factor (polyakQ μ L) := by
    rcases lt_or_eq_of_le hc with h | h
    · exact (Spiral.one_lt_factor (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) h).le
    · rw [← h,Spiral.factor_critical]
  have hd : 0 < c₀*‖x₀‖ := mul_pos hc₀ (norm_pos_iff.mpr hx)
  have hlower (N : ℕ) : c₀*‖x₀‖ ≤ ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
    have hp : (1 : ℝ) ≤ Spiral.factor (polyakQ μ L)^N := one_le_pow₀ hfac
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ c₀*‖x₀‖ by positivity)
    calc
      c₀*‖x₀‖ ≤ c₀*Spiral.factor (polyakQ μ L)^N*‖x₀‖ := by
        simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hm
      _ ≤ _ := hbound N
  refine ⟨f,hf,x₀,hx,fun hlim => ?_⟩
  have hn : Tendsto (fun N => ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖)
      atTop (𝓝 0) := by simpa only [norm_zero] using hlim.norm
  have hh : c₀*‖x₀‖ ≤ 0 := ge_of_tendsto hn (Eventually.of_forall hlower)
  linarith

/-- Article: one actual source example diverges exponentially above the threshold. -/
theorem exists_divergent_example {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : criticalQ < polyakQ μ L) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, x₀ ≠ 0 ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
        (∀ N : ℕ, c₀*Spiral.factor (polyakQ μ L)^N*‖x₀‖ ≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖) ∧
        Tendsto (fun N => ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖) atTop atTop := by
  obtain ⟨f,hf,x₀,hx,c₀,hc₀,hbound⟩ := exists_spiral_example hμ hL
  have hfac := Spiral.one_lt_factor (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hc
  have hd : 0 < c₀*‖x₀‖ := mul_pos hc₀ (norm_pos_iff.mpr hx)
  refine ⟨f,hf,x₀,hx,c₀,hc₀,hbound,?_⟩
  have hlim := (tendsto_pow_atTop_atTop_of_one_lt hfac).const_mul_atTop hd
  apply tendsto_atTop_mono _ hlim
  intro N
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound N

end polyak.Threshold
