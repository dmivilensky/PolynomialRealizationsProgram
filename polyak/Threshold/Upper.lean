import polyak.Threshold.Strip
import polyak.Threshold.Parameters
import polyak.Growth.SpectralUpper
import polyak.Waves.Polyak

/-!
Article: Appendix B, proof of the sharp convergence threshold, upper direction.
Use: exact growth-exponent feasibility and the proved threshold strip already
give the strict subcritical rate and its stated square-root upper bound.
Proof: apply the strip at log ρΓ; no classification or conjectured worst wave is used.
-/

noncomputable section

open scoped goldenRatio

namespace polyak.Threshold

open Spectral Growth Dynamics

/-- Article: the exact free-state growth factor at Polyak's normalized coefficients. -/
def polyakGrowthRate (q : ℝ) : ℝ := growthRate 0 (2*q) (q^2)

/-- Article: spectral feasibility at the true growth exponent. -/
theorem exists_feasible_at_polyak_growth {q : ℝ} (hq : 0 < q) :
    ∃ ν C, Feasible (Real.log (polyakGrowthRate q)-Real.log q)
      (Real.log (polyakGrowthRate q)) ν C := by
  obtain ⟨ν,C,h⟩ := exists_feasible_at_growth (A := 0) (B := 2*q) (β := q^2)
    (by positivity)
  rw [Waves.multiplierMap_polyak q _ hq,Waves.mixtureFeasible_polyak_iff] at h
  exact ⟨ν,C,h⟩

/-- Article: log q_c=−log φ. -/
theorem log_criticalQ : Real.log criticalQ = -Real.log φ := by
  exact Real.log_inv φ

/-- Article: strict subcritical growth, before any algebraic classification. -/
theorem polyakGrowthRate_lt_one {q : ℝ} (hq : 0 < q) (hc : q < criticalQ) :
    polyakGrowthRate q < 1 := by
  obtain ⟨ν,C,h⟩ := exists_feasible_at_polyak_growth hq
  have hs := feasible_strip h
  have hqlog := Real.log_lt_log hq hc
  rw [log_criticalQ] at hqlog
  have hp : 0 < polyakGrowthRate q := growthRate_pos _ _ _
  by_contra hh
  have hrate : 1 ≤ polyakGrowthRate q := le_of_not_gt hh
  have ht : 0 ≤ Real.log (polyakGrowthRate q) := Real.log_nonneg hrate
  rw [abs_of_nonneg ht] at hs
  have hv := le_abs_self (Real.log (polyakGrowthRate q)-Real.log q)
  linarith

/-- Article: at the critical factor the free-state rate is at most one. -/
theorem polyakGrowthRate_critical_le_one : polyakGrowthRate criticalQ ≤ 1 := by
  obtain ⟨ν,C,h⟩ := exists_feasible_at_polyak_growth criticalQ_pos
  by_contra hh
  have hrate : 1 < polyakGrowthRate criticalQ := lt_of_not_ge hh
  have ht : 0 < Real.log (polyakGrowthRate criticalQ) := Real.log_pos hrate
  have hs := feasible_strip_strict h ht.ne'
  rw [abs_of_pos ht,log_criticalQ] at hs
  simp only [sub_neg_eq_add] at hs
  have hv := le_abs_self (Real.log (polyakGrowthRate criticalQ)+Real.log φ)
  linarith

/-- Article: ρΓ≤sqrt(φq) below the threshold. -/
theorem polyakGrowthRate_le_sqrt {q : ℝ} (hq : 0 < q) (hc : q < criticalQ) :
    polyakGrowthRate q ≤ Real.sqrt (φ*q) := by
  obtain ⟨ν,C,h⟩ := exists_feasible_at_polyak_growth hq
  have hs := feasible_strip h
  have hp : 0 < polyakGrowthRate q := growthRate_pos _ _ _
  have ht : Real.log (polyakGrowthRate q) < 0 := Real.log_neg hp (polyakGrowthRate_lt_one hq hc)
  rw [abs_of_neg ht] at hs
  have hv := le_abs_self (Real.log (polyakGrowthRate q)-Real.log q)
  have hlog : 2*Real.log (polyakGrowthRate q) ≤ Real.log φ+Real.log q := by linarith
  have hexp := Real.exp_le_exp.mpr hlog
  have he : Real.exp (2*Real.log (polyakGrowthRate q)) = polyakGrowthRate q^2 := by
    rw [show 2*Real.log (polyakGrowthRate q)=Real.log (polyakGrowthRate q)+Real.log (polyakGrowthRate q) by ring,
      Real.exp_add,Real.exp_log hp,pow_two]
  rw [he,Real.exp_add,Real.exp_log Real.goldenRatio_pos,Real.exp_log hq] at hexp
  have hsq := Real.sq_sqrt (mul_pos Real.goldenRatio_pos hq).le
  have hn := Real.sqrt_nonneg (φ*q)
  nlinarith

/-- Article: the original from-rest rate is controlled by the proved Polyak free-state rate. -/
theorem original_polyakRate_le_growth {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    rate μ L (polyakAlpha μ L) (polyakBeta μ L) ≤ polyakGrowthRate (polyakQ μ L) := by
  have h := originalRate_le_growthRate hμ hL (polyakAlpha_pos hμ hL) (polyakBeta_mem hμ hL).1
  rwa [polyak_normalizedA hμ hL,polyak_normalizedB hμ hL] at h

/-- Article: the exact original rate is strictly below one whenever q<q_c. -/
theorem original_polyakRate_lt_one {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : polyakQ μ L < criticalQ) :
    rate μ L (polyakAlpha μ L) (polyakBeta μ L) < 1 :=
  (original_polyakRate_le_growth hμ hL).trans_lt (polyakGrowthRate_lt_one (polyakQ_pos hμ hL) hc)

/-- Article: the stated upper bound applies to the original from-rest supremum over all dimensions. -/
theorem original_polyakRate_le_sqrt {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : polyakQ μ L < criticalQ) :
    rate μ L (polyakAlpha μ L) (polyakBeta μ L) ≤ Real.sqrt (φ*polyakQ μ L) :=
  (original_polyakRate_le_growth hμ hL).trans (polyakGrowthRate_le_sqrt (polyakQ_pos hμ hL) hc)

end polyak.Threshold
