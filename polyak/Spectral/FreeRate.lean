import polyak.Spectral.Optimal

/-!
Article: Theorem spectral, equality of the original and free-state Polyak rates.
Use: express both exact rates directly in the original curvature parameters.
Proof: the normalization dictionary identifies the actual recurrence with
the free-segment rate, and both proved rates equal the attained spectral maximum.
-/

namespace polyak.Spectral

noncomputable section

/-- Article: the free-state rate in the original Polyak parameters is exp T(q). -/
theorem polyakGrowthRate_eq_exp_T {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    Growth.growthRate
      (Dynamics.normalizedA μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L))
      (Dynamics.normalizedB μ L (Dynamics.polyakAlpha μ L))
      (Dynamics.polyakBeta μ L) = Real.exp (T (Dynamics.polyakQ μ L)) := by
  rw [Dynamics.polyak_normalizedA hμ hL,Dynamics.polyak_normalizedB hμ hL]
  exact freeRate_eq_exp_T (Dynamics.polyakQ_pos hμ hL)

/-- Article: the genuine free-segment rate equals the original worst-case rate
with its prescribed zero initial impulse. -/
theorem polyakGrowthRate_eq_originalRate {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    Growth.growthRate
      (Dynamics.normalizedA μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L))
      (Dynamics.normalizedB μ L (Dynamics.polyakAlpha μ L))
      (Dynamics.polyakBeta μ L) =
        Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) := by
  rw [polyakGrowthRate_eq_exp_T hμ hL,originalRate_eq_exp_T hμ hL]

end
end polyak.Spectral
