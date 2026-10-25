import polyak.FareyPlateau.Edge.Adjacent
import polyak.ModeLocking.Localization.Shift

/-! The non-strict edge certificate identifies the threshold even when its
zeros or curvatures are degenerate. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking Set Filter MeasureTheory
open scoped BigOperators Topology

namespace AdjacentData
variable {q : Tuning} {j k : ℕ} (A : AdjacentData q j k)

theorem weight_positive {n : ℤ} (hn : n ∈ A.lags) : 0 < A.weight n := by
  simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · simp only [weight, ite_true]; linarith [A.mix_lt]
  · simpa only [weight, ite_eq_right A.lower_ne_upper.symm] using A.mix_pos

theorem weight_normalized : ∑ n ∈ A.lags, A.weight n = 1 := by
  simp only [lags, Finset.sum_pair A.lower_ne_upper, weight, ite_true,
    ite_eq_right A.lower_ne_upper.symm]
  ring

theorem pinning_positive {x : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    0 < pinningPolynomial A.lags A.weight x := by
  have hnn : 0 ≤ pinningPolynomial A.lags A.weight x :=
    Finset.sum_nonneg (fun n hn => mul_nonneg (A.weight_positive hn).le
      (sub_nonneg.mpr (Real.cos_le_one _)))
  by_contra hnot
  have hz : pinningPolynomial A.lags A.weight x = 0 := le_antisymm (le_of_not_gt hnot) hnn
  have hcos (n : ℤ) (hn : n ∈ A.lags) : Real.cos ((n : ℝ) * x) = 1 := by
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun n hn =>
      mul_nonneg (A.weight_positive hn).le (sub_nonneg.mpr (Real.cos_le_one _)))).mp hz n hn
    have he := (mul_eq_zero.mp ht).resolve_left (A.weight_positive hn).ne'
    linarith
  obtain ⟨a, ha⟩ := (Real.cos_eq_one_iff _).mp (hcos A.lower (by simp [lags]))
  obtain ⟨b, hb⟩ := (Real.cos_eq_one_iff _).mp (hcos A.upper (by simp [lags]))
  have hres := A.residue A.lower (by simp [lags])
  have hl := Int.emod_add_ediv_mul (A.lower * j) (k : ℤ)
  rw [hres] at hl
  have hlR : 1 + (((A.lower * j) / k : ℤ) : ℝ) * k = (A.lower : ℝ) * j := by exact_mod_cast hl
  let c : ℤ := (j : ℤ) * a - ((A.lower * j) / k) * (b - a)
  have he : x = (c : ℝ) * (2 * Real.pi) := by
    have hb' : (b : ℝ) * (2 * Real.pi) = ((A.lower : ℝ) + k) * x := by
      simpa only [upper, Int.cast_add, Int.cast_natCast] using hb
    dsimp [c]
    push_cast
    linear_combination -(j : ℝ) * ha + (((A.lower * j) / k : ℤ) : ℝ) * (hb' - ha) + x * hlR
  have hcpos : (0 : ℝ) < c := by nlinarith [Real.pi_pos]
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by exact_mod_cast hcpos)
  nlinarith [Real.pi_pos]

theorem phase_curve : Geometry.shiftedCurve q A.edgeShift A.frequency = Real.pi / k := by
  change Geometry.shiftedAngle q A.edgeShift A.frequency = _
  exact phase_at_shift q A.period_ge
    ⟨atom_pos A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le,
      atom_lt_pi (by have := A.period_ge; omega) A.numerator_lt⟩

theorem single_feasible : ProgramSolution (Geometry.shiftedCurve q A.edgeShift) nonzeroLags
    (Measure.dirac A.frequency) := by
  refine ⟨inferInstance, by simp, ?_, ?_⟩
  · rw [integral_dirac]
    change 0 ≤ Real.cos (Geometry.shiftedCurve q A.edgeShift A.frequency)
    rw [A.phase_curve]
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
    exact (Real.cos_pos_of_mem_Ioo ⟨by
        have hp : 0 < Real.pi / k := by positivity
        linarith [Real.pi_pos],
      (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos])⟩).le
  · intro n _hn
    rw [integral_dirac]
    have hh := lag_position_one (by have := A.period_ge; omega) A.numerator_lt.le _ A.phase_curve n
    change 0 ≤ (Geometry.shiftedCurve q A.edgeShift).lag n (atom j k (by have := A.period_ge; omega) A.numerator_lt.le)
    rw [hh]
    have hkZ : (0 : ℤ) < k := by have := A.period_ge; omega
    by_cases hz : (n * j) % k = 0
    · simp only [hz, Int.cast_zero, Farey.positionValue_zero, le_refl]
    · have hp : 0 < (n * j) % k := by
        have := Int.emod_nonneg (n * j) hkZ.ne'
        omega
      exact (Farey.positionValue_nonneg_iff hkZ (by norm_num)
        (by exact_mod_cast (show 1 ≤ k by have := A.period_ge; omega))
        (by exact_mod_cast hp) (by exact_mod_cast Int.emod_lt_of_pos (n * j) hkZ)).mpr
        (by exact_mod_cast (show 1 ≤ (n * j) % k by omega))

theorem single_periodic : PeriodicFP (Geometry.shiftedCurve q A.edgeShift) k := by
  refine ⟨Measure.dirac A.frequency, A.single_feasible, ?_⟩
  rw [ae_dirac_eq]
  apply Filter.eventually_pure.mpr
  exact atom_grid A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le

theorem shift_identity (t : ℝ) (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier) :
    finiteSymbol q t A.lags A.weight ω / Real.sin (Geometry.shiftedCurve q t ω) =
      finiteSymbol q A.edgeShift A.lags A.weight ω / Real.sin (Geometry.shiftedCurve q A.edgeShift ω) +
        (t - A.edgeShift) * pinningPolynomial A.lags A.weight ω := by
  have he := Localization.shift_identity q t A.edgeShift
    (fun n : {n // n ∈ A.lags} => n.val) (fun n => A.weight n.val) 0 ω hω
  simp only [Localization.symbol, Localization.oscillation, zero_mul, add_zero] at he
  rw [Finset.sum_coe_sort A.lags (fun n => A.weight n * (Geometry.shiftedCurve q t).lag n ω),
    Finset.sum_coe_sort A.lags (fun n => A.weight n * (Geometry.shiftedCurve q A.edgeShift).lag n ω),
    Finset.sum_coe_sort A.lags (fun n => A.weight n * (1 - Real.cos ((n : ℝ) * (ω : ℝ))))] at he
  simpa only [finiteSymbol_actual, pinningPolynomial] using he

theorem symbol_negative_below
    (hF : ∀ x ∈ Icc (0 : ℝ) Real.pi, 0 ≤ A.function x)
    {t : ℝ} (ht : t < A.edgeShift) (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier) :
    finiteSymbol q t A.lags A.weight ω < 0 := by
  have hs := Localization.phase_sin_pos q A.edgeShift ω hω
  have htphase := Localization.phase_sin_pos q t ω hω
  have hval : finiteSymbol q A.edgeShift A.lags A.weight ω ≤ 0 := by
    rw [A.finiteSymbol_eq]
    nlinarith [hF ω ω.property]
  have hquot := div_nonpos_of_nonpos_of_nonneg hval hs.le
  have hshift := mul_neg_of_neg_of_pos (sub_neg.mpr ht) (A.pinning_positive hω.1 ω.property.2)
  have he := A.shift_identity t ω hω
  have hh : finiteSymbol q t A.lags A.weight ω / Real.sin (Geometry.shiftedCurve q t ω) < 0 := by linarith
  simpa only [zero_mul] using (div_lt_iff₀ htphase).mp hh

end AdjacentData
end polyak.FareyPlateau.Edge
