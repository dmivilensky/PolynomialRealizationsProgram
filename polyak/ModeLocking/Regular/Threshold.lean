import polyak.ModeLocking.Regular.Extremals
import polyak.ModeLocking.Localization.Shift
import polyak.Levels.Threshold.PeriodicThreshold

/-! Regular primary data identify the full threshold and every relaxation
containing their lags. No analytic continuation hypothesis is used here. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels MeasureTheory
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem symbol_shift_identity (t : ℝ) (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier) :
    finiteSymbol q t D.lags D.dual ω / Real.sin (Geometry.shiftedCurve q t ω) =
      finiteSymbol q s D.lags D.dual ω / Real.sin (Geometry.shiftedCurve q s ω) +
        (t - s) * pinningPolynomial D.lags D.dual ω := by
  have he := Localization.shift_identity q t s (fun n : {n // n ∈ D.lags} => n.val)
    (fun n => D.dual n.val) 0 ω hω
  simp only [Localization.symbol, Localization.oscillation, zero_mul, add_zero] at he
  rw [Finset.sum_coe_sort D.lags (fun n => D.dual n * (Geometry.shiftedCurve q t).lag n ω),
    Finset.sum_coe_sort D.lags (fun n => D.dual n * (Geometry.shiftedCurve q s).lag n ω),
    Finset.sum_coe_sort D.lags (fun n => D.dual n * (1 - Real.cos ((n : ℝ) * (ω : ℝ))))] at he
  simpa only [finiteSymbol_actual, pinningPolynomial] using he

theorem pinning_nonneg (x : ℝ) : 0 ≤ pinningPolynomial D.lags D.dual x :=
  Finset.sum_nonneg fun n hn => mul_nonneg (D.dual_pos n hn).le
    (sub_nonneg.mpr (Real.cos_le_one _))

theorem symbol_negative_below {t : ℝ} (ht : t < s) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) : finiteSymbol q t D.lags D.dual ω < 0 := by
  have hs := Localization.phase_sin_pos q s ω hω
  have htphase := Localization.phase_sin_pos q t ω hω
  have he := D.symbol_shift_identity t ω hω
  have hleft : finiteSymbol q t D.lags D.dual ω / Real.sin (Geometry.shiftedCurve q t ω) < 0 := by
    by_cases hz : finiteSymbol q s D.lags D.dual ω = 0
    · obtain h0 | ⟨i, hi⟩ := (D.symbol_zero_iff ω).mp hz
      · simp only [h0, frequencyZero] at hω
        exact (lt_irrefl 0 hω.1).elim
      · rw [he, hz, zero_div, zero_add, hi]
        exact mul_neg_of_neg_of_pos (sub_neg.mpr ht) (D.pinning_pos i)
    · have hn := lt_of_le_of_ne (D.symbol_nonpos ω ω.property) hz
      rw [he]
      exact add_neg_of_neg_of_nonpos (div_neg_of_neg_of_pos hn hs)
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.le) (D.pinning_nonneg ω))
  simpa only [zero_mul] using (div_lt_iff₀ htphase).mp hleft

theorem infeasible_below {t : ℝ} (ht : t < s) {N' : Set ℤ}
    (hN : (D.lags : Set ℤ) ⊆ N') : ¬ FPOn (Geometry.shiftedCurve q t) N' := by
  rintro ⟨w, hw⟩
  let u := w.restrict Threshold.interiorCarrier
  have hu : ProgramSolution (Geometry.shiftedCurve q t) N' u := hw.remove_endpoints
  let : IsFiniteMeasure u := hu.1
  let : NeZero u := ⟨hu.2.1⟩
  let c : CertificateSymbol (Geometry.shiftedCurve q t) (D.lags : Set ℤ) := {
    lags := D.lags
    lags_subset := by simp
    weight := D.dual
    weight_nonneg := fun n hn => (D.dual_pos n hn).le
    gamma := 0
    gamma_nonneg := le_rfl }
  have hc : Global.Symbols.total c = 1 := by
    simp only [Global.Symbols.total, c, D.dual_sum, add_zero]
  let a := Global.Symbols.normalizeWeights c (by rw [hc]; norm_num)
  have hae (ω : Frequency) : a.eval (Geometry.shiftedCurve q t) ω = finiteSymbol q t D.lags D.dual ω := by
    rw [Global.Symbols.normalizeWeights_eval, hc, div_one, finiteSymbol_actual]
    simp only [CertificateSymbol.eval, c, zero_mul, add_zero]
  have hcar : ∀ᵐ ω ∂u, ω ∈ Threshold.interiorCarrier := ae_restrict_mem Threshold.measurableSet_interiorCarrier
  have hn : ∀ᵐ ω ∂u, a.eval (Geometry.shiftedCurve q t) ω < 0 :=
    hcar.mono fun ω hω => by rw [hae]; exact D.symbol_negative_below ht ω hω
  have hi := a.integrable_eval (Geometry.shiftedCurve q t) u
  have hnonneg := a.integral_nonneg_of_solution (hu.relax hN)
  have hnonpos : (∫ ω, a.eval (Geometry.shiftedCurve q t) ω ∂u) ≤ 0 :=
    integral_nonpos_of_ae (hn.mono fun _ h => h.le)
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hn.mono fun _ h => neg_nonneg.mpr h.le) hi.neg).mp
    (by rw [integral_neg]; linarith)
  obtain ⟨ω, hω, hzero⟩ := (hn.and hz).exists
  change -a.eval (Geometry.shiftedCurve q t) ω = 0 at hzero
  linarith

include D in
theorem sigma_eq : Threshold.sigma q = s := by
  apply le_antisymm
  · exact (Threshold.shifted_fp_iff q s).mp D.periodic_feasible.fp
  · by_contra hn
    have ht : Threshold.sigma q < s := lt_of_not_ge hn
    exact D.infeasible_below ht (fun n hn => D.lags_nonzero n hn) (Threshold.sigma_feasible q)

include D in
theorem sigmaPeriodic_eq : Threshold.sigmaPeriodic q L = s := by
  apply le_antisymm
  · exact (Threshold.shifted_periodic_iff q D.period_ge s).mp D.periodic_feasible
  · rw [← D.sigma_eq]
    exact Threshold.sigma_le_sigmaPeriodic q D.period_ge

include D in
theorem sigmaOn_eq {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N') (hN' : N' ⊆ nonzeroLags) :
    Threshold.sigmaOn q N' = s := by
  apply le_antisymm
  · rw [← D.sigma_eq]
    exact Threshold.sigmaOn_le_sigma q N' hN'
  · by_contra hn
    exact D.infeasible_below (lt_of_not_ge hn) hN (Threshold.sigmaOn_feasible q N' hN')

end polyak.ModeLocking.RegularData
