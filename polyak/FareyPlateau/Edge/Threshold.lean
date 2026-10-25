import polyak.FareyPlateau.Edge.WeakCriterion

/-! The non-strict source criterion and the full extremal classification
under a strict complement, without assuming nondegenerate curvatures. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking Set Filter MeasureTheory
open scoped BigOperators Topology

namespace AdjacentData
variable {q : Tuning} {j k : ℕ} (A : AdjacentData q j k)

def dualCertificate (t : ℝ) : CertificateSymbol (Geometry.shiftedCurve q t) nonzeroLags where
  lags := A.lags
  lags_subset := by
    intro n hn
    simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact A.lower_nonzero
    · exact A.upper_nonzero
  weight := A.weight
  weight_nonneg := fun n hn => (A.weight_positive hn).le
  gamma := 0
  gamma_nonneg := le_rfl

theorem dual_total (t : ℝ) : Global.Symbols.total (A.dualCertificate t) = 1 := by
  simp only [Global.Symbols.total, dualCertificate, A.weight_normalized, add_zero]

def dualWeights (t : ℝ) : Global.Symbols.Weights nonzeroLags :=
  Global.Symbols.normalizeWeights (A.dualCertificate t) (by rw [A.dual_total]; norm_num)

theorem dual_eval (t : ℝ) (ω : Frequency) :
    (A.dualWeights t).eval (Geometry.shiftedCurve q t) ω = finiteSymbol q t A.lags A.weight ω := by
  rw [dualWeights, Global.Symbols.normalizeWeights_eval, A.dual_total, div_one, finiteSymbol_actual]
  simp only [CertificateSymbol.eval, dualCertificate, zero_mul, add_zero]

theorem infeasible_below (hF : ∀ x ∈ Icc (0 : ℝ) Real.pi, 0 ≤ A.function x)
    {t : ℝ} (ht : t < A.edgeShift) : ¬ FP (Geometry.shiftedCurve q t) := by
  rintro ⟨w, hw⟩
  let u := w.restrict Threshold.interiorCarrier
  have hu : ProgramSolution (Geometry.shiftedCurve q t) nonzeroLags u := hw.remove_endpoints
  let : IsFiniteMeasure u := hu.1
  let : NeZero u := ⟨hu.2.1⟩
  have hcar : ∀ᵐ ω ∂u, ω ∈ Threshold.interiorCarrier := ae_restrict_mem Threshold.measurableSet_interiorCarrier
  have hn : ∀ᵐ ω ∂u, (A.dualWeights t).eval (Geometry.shiftedCurve q t) ω < 0 :=
    hcar.mono fun ω hω => by rw [A.dual_eval]; exact A.symbol_negative_below hF ht ω hω
  have hi := (A.dualWeights t).integrable_eval (Geometry.shiftedCurve q t) u
  have hnonneg := (A.dualWeights t).integral_nonneg_of_solution hu
  have hnonpos : (∫ ω, (A.dualWeights t).eval (Geometry.shiftedCurve q t) ω ∂u) ≤ 0 :=
    integral_nonpos_of_ae (hn.mono fun _ h => h.le)
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hn.mono fun _ h => neg_nonneg.mpr h.le) hi.neg).mp
    (by rw [integral_neg]; linarith)
  obtain ⟨ω, hω, hzero⟩ := (hn.and hz).exists
  change -(A.dualWeights t).eval (Geometry.shiftedCurve q t) ω = 0 at hzero
  linarith

theorem threshold (hF : ∀ x ∈ Icc (0 : ℝ) Real.pi, 0 ≤ A.function x) :
    Threshold.sigma q = A.edgeShift ∧ Threshold.sigmaPeriodic q k = A.edgeShift := by
  have hs : Threshold.sigma q = A.edgeShift := by
    apply le_antisymm
    · exact (Threshold.shifted_fp_iff q A.edgeShift).mp A.single_periodic.fp
    · by_contra hn
      exact A.infeasible_below hF (lt_of_not_ge hn) (Threshold.sigma_feasible q)
  refine ⟨hs, le_antisymm ?_ ?_⟩
  · exact (Threshold.shifted_periodic_iff q A.period_ge A.edgeShift).mp A.single_periodic
  · rw [← hs]
    exact Threshold.sigma_le_sigmaPeriodic q A.period_ge

theorem strict_complement_carried
    (hstrict : ∀ x : ℝ, 0 < x → x ≤ Real.pi → x ≠ (A.frequency : ℝ) → 0 < A.function x)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q A.edgeShift) nonzeroLags w) :
    ∀ᵐ ω ∂w, ω = A.frequency ∨ ω = frequencyZero := by
  have hnonpos (ω : Frequency) : (A.dualWeights A.edgeShift).eval (Geometry.shiftedCurve q A.edgeShift) ω ≤ 0 := by
    rw [A.dual_eval, A.finiteSymbol_eq]
    change -2 * A.function (ω : ℝ) ≤ 0
    by_cases h0 : (ω : ℝ) = 0
    · rw [h0, A.endpoint_zero]; norm_num
    by_cases hfreq : (ω : ℝ) = (A.frequency : ℝ)
    · rw [hfreq, A.value_zero]; norm_num
    have hpos := hstrict ω (lt_of_le_of_ne ω.property.1 (Ne.symm h0)) ω.property.2 hfreq
    nlinarith
  have hcar := (A.dualWeights A.edgeShift).solution_carried_zero hnonpos hw
  filter_upwards [hcar] with ω hω
  by_cases h0 : ω = frequencyZero
  · exact Or.inr h0
  by_cases hfreq : ω = A.frequency
  · exact Or.inl hfreq
  have hx : 0 < (ω : ℝ) := by
    apply lt_of_le_of_ne ω.property.1
    intro he
    exact h0 (Subtype.ext he.symm)
  have hneq : (ω : ℝ) ≠ (A.frequency : ℝ) := fun he => hfreq (Subtype.ext he)
  rw [A.dual_eval, A.finiteSymbol_eq] at hω
  have := hstrict ω hx ω.property.2 hneq
  linarith

theorem strict_complement_classification
    (hstrict : ∀ x : ℝ, 0 < x → x ≤ Real.pi → x ≠ (A.frequency : ℝ) → 0 < A.function x)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q A.edgeShift) nonzeroLags w) :
    ∃ b a : NNReal, 0 < b ∧
      w = (b : ENNReal) • Measure.dirac A.frequency +
        (a : ENNReal) • Measure.dirac frequencyZero ∧
      (a : ℝ) ≤ (b : ℝ) * Real.cos (Real.pi / k) := by
  let : IsFiniteMeasure w := hw.1
  let b : NNReal := (w {A.frequency}).toNNReal
  let a : NNReal := (w {frequencyZero}).toNNReal
  have hfreq : A.frequency ≠ frequencyZero := by
    intro he
    have hp := atom_pos A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le
    change 0 < (A.frequency : ℝ) at hp
    simp only [he, frequencyZero] at hp
    exact lt_irrefl _ hp
  have he : w = (b : ENNReal) • Measure.dirac A.frequency +
      (a : ENNReal) • Measure.dirac frequencyZero := by
    have hh := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac hfreq).mp (A.strict_complement_carried hstrict hw)
    simpa only [b, a, ENNReal.coe_toNNReal (measure_ne_top _ _)] using hh
  let : IsFiniteMeasure ((b : ENNReal) • Measure.dirac A.frequency) :=
    (Measure.dirac A.frequency).smul_finite ENNReal.coe_ne_top
  let : IsFiniteMeasure ((a : ENNReal) • Measure.dirac frequencyZero) :=
    (Measure.dirac frequencyZero).smul_finite ENNReal.coe_ne_top
  have hbnd : (a : ℝ) ≤ (b : ℝ) * Real.cos (Real.pi / k) := by
    have hh := hw.2.2.1
    rw [he, integral_add_measure
      ((Geometry.shiftedCurve q A.edgeShift).continuous_minimizer.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((Geometry.shiftedCurve q A.edgeShift).continuous_minimizer.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac] at hh
    simp only [ENNReal.coe_toReal, smul_eq_mul, Curve.minimizer_at_zero, mul_neg, mul_one] at hh
    change 0 ≤ (b : ℝ) * Real.cos (Geometry.shiftedCurve q A.edgeShift A.frequency) - (a : ℝ) at hh
    rw [A.phase_curve] at hh
    linarith
  have hbpos : 0 < b := by
    apply lt_of_le_of_ne (show 0 ≤ b from zero_le)
    intro hz
    have hb0 : b = 0 := hz.symm
    have ha0 : a = 0 := by
      apply NNReal.coe_injective
      simp only [hb0, NNReal.coe_zero, zero_mul] at hbnd
      exact le_antisymm hbnd a.coe_nonneg
    apply hw.2.1
    simpa only [hb0, ha0, ENNReal.coe_zero, zero_smul, add_zero] using he
  exact ⟨b, a, hbpos, he, hbnd⟩

end AdjacentData
end polyak.FareyPlateau.Edge
