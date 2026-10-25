import polyak.Threshold.Convergence
import polyak.Threshold.Counterexamples
import polyak.Threshold.Cycle

/-!
Article: Theorem threshold and Proposition thresholdstrip at t=0.
Use: close the exact source condition-number threshold, including its iff
convergence statement and the stated uniform square-root upper rate.
-/

noncomputable section

open Filter
open scoped Topology goldenRatio

namespace polyak.Threshold

open Dynamics Spectral

/-- Article: the critical three-cycle is optimal at zero exponent. -/
theorem V_zero : V 0=Real.log φ := by
  apply le_antisymm
  · obtain ⟨ν,C,h⟩ := V_mem 0
    have hs := feasible_strip h
    simpa only [abs_of_nonneg (V_nonneg 0),abs_zero,zero_add] using hs
  · exact (isGreatest_V 0).2 ⟨Spiral.spectrum 0,0,Spiral.critical_feasible⟩

/-- Article: subcritical source rate, expressed directly in the original condition number. -/
theorem rate_lt_one_of_condition {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : L/μ < criticalKappa) : rate μ L (polyakAlpha μ L) (polyakBeta μ L) < 1 := by
  apply original_polyakRate_lt_one hμ hL
  rw [polyakQ_eq_conditionQ hμ hL]
  exact (conditionQ_lt_critical_iff ((one_lt_div hμ).mpr hL)).mpr hc

/-- Article: exact critical source rate. -/
theorem rate_eq_one_of_condition {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : L/μ = criticalKappa) : rate μ L (polyakAlpha μ L) (polyakBeta μ L) = 1 := by
  apply original_polyakRate_critical hμ hL
  rw [polyakQ_eq_conditionQ hμ hL]
  exact (conditionQ_eq_critical_iff ((one_lt_div hμ).mpr hL)).mpr hc

/-- Article: supercritical source rate. -/
theorem one_lt_rate_of_condition {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : criticalKappa < L/μ) : 1 < rate μ L (polyakAlpha μ L) (polyakBeta μ L) := by
  apply one_lt_original_polyakRate hμ hL
  rw [polyakQ_eq_conditionQ hμ hL]
  exact (critical_lt_conditionQ_iff ((one_lt_div hμ).mpr hL)).mpr hc

/-- Article: all three strict/equality rate regimes, with the exact printed κ_c. -/
theorem sharp_rate_threshold {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    (rate μ L (polyakAlpha μ L) (polyakBeta μ L) < 1 ↔ L/μ < criticalKappa) ∧
    (rate μ L (polyakAlpha μ L) (polyakBeta μ L) = 1 ↔ L/μ = criticalKappa) ∧
    (1 < rate μ L (polyakAlpha μ L) (polyakBeta μ L) ↔ criticalKappa < L/μ) := by
  rcases lt_trichotomy (L/μ) criticalKappa with h | h | h
  · have hr := rate_lt_one_of_condition hμ hL h
    constructor
    · exact ⟨fun _ => h,fun _ => hr⟩
    · constructor
      · constructor <;> intro hh <;> linarith
      · constructor <;> intro hh <;> linarith
  · have hr := rate_eq_one_of_condition hμ hL h
    constructor
    · constructor <;> intro hh <;> linarith
    · constructor
      · exact ⟨fun _ => h,fun _ => hr⟩
      · constructor <;> intro hh <;> linarith
  · have hr := one_lt_rate_of_condition hμ hL h
    constructor
    · constructor <;> intro hh <;> linarith
    · constructor
      · constructor <;> intro hh <;> linarith
      · exact ⟨fun _ => h,fun _ => hr⟩

/-- Article: the stated source-rate upper bound below the threshold. -/
theorem rate_le_sqrt_of_condition {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : L/μ < criticalKappa) :
    rate μ L (polyakAlpha μ L) (polyakBeta μ L) ≤ Real.sqrt (φ*polyakQ μ L) := by
  apply original_polyakRate_le_sqrt hμ hL
  rw [polyakQ_eq_conditionQ hμ hL]
  exact (conditionQ_lt_critical_iff ((one_lt_div hμ).mpr hL)).mpr hc

/-- Article: convergence on all source functions and starts iff κ<κ_c.
Use: the reverse direction is refuted by one true three-dimensional from-rest example. -/
theorem converges_on_all_iff {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    (∀ d : ℕ, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
      SmoothStronglyConvex μ L f → ∀ a, (∀ y,f a ≤ f y) → ∀ x₀,
        Tendsto (iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀) atTop (𝓝 a)) ↔
      L/μ < criticalKappa := by
  constructor
  · intro hall
    by_contra hc
    have hκ := (one_lt_div hμ).mpr hL
    have hq : criticalQ ≤ polyakQ μ L := by
      rw [polyakQ_eq_conditionQ hμ hL]
      exact le_of_not_gt (fun hh => hc ((conditionQ_lt_critical_iff hκ).mp hh))
    obtain ⟨f,hf,x₀,_,hnot⟩ := exists_nonconvergent_example hμ hL hq
    exact hnot (hall 3 f hf.toSmoothStronglyConvex 0
      ((hf.toSmoothStronglyConvex.minimizer_iff 0).mpr hf.gradient_zero) x₀)
  · intro hc d f hf a hmin x₀
    exact polyak_converges_of_condition hf a hmin hc x₀

end polyak.Threshold
