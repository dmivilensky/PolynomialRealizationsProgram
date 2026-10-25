import polyak.Levels.Realization.Lower
import polyak.Levels.Program.SpectralBridge
import polyak.Levels.Program.Alternative
import polyak.General.OneExponent

/-! Article: Theorem exactthr, the complete threshold alternative for the
original worst-case rate, with all measures and every signed integer lag. -/
namespace polyak.Levels
noncomputable section
open Dynamics

theorem fp_worstAll_lower (q : General.Tuning) (h : FP (tuningCurve q)) :
    ∃c : ℝ,0<c ∧ ∀N : ℕ,c≤worstAll q.x q.y 1 q.beta N := by
  obtain ⟨ν,hν⟩:=(threshold_spectral_iff_fp q).mpr h
  apply Realization.threshold_spectrum_worstAll_lower q.x_pos q.x_lt_y
    (by norm_num) q.beta_nonneg q.beta_lt_one (by simpa using q.y_lt) ν
  simpa only [q.normalizedA_eq,q.normalizedB_eq] using hν

theorem fp_one_le_rate (q : General.Tuning) (h : FP (tuningCurve q)) : 1≤q.rate := by
  obtain ⟨ν,hν⟩:=(threshold_spectral_iff_fp q).mpr h
  apply Realization.one_le_rate_of_threshold_spectrum q.x_pos q.x_lt_y
    (by norm_num) q.beta_nonneg q.beta_lt_one (by simpa using q.y_lt) ν
  simpa only [q.normalizedA_eq,q.normalizedB_eq] using hν

theorem rate_lt_one_iff_infeasible (q : General.Tuning) :
    q.rate<1 ↔ ¬FP (tuningCurve q) := by
  constructor
  · intro h hFP
    exact (not_lt_of_ge (fp_one_le_rate q hFP)) h
  · intro h
    apply q.infeasible_zero_rate_lt_one
    exact fun hν=>h ((threshold_spectral_C_iff_fp q).mp hν)

theorem rate_lt_one_iff_strictSymbol (q : General.Tuning) :
    q.rate<1 ↔ Nonempty (StrictSymbol (tuningCurve q) nonzeroLags) := by
  rw [rate_lt_one_iff_infeasible]
  exact infeasible_iff_strictSymbol _ _

end
end polyak.Levels
