import polyak.ModeLocking.Localization.Endpoints
import polyak.ModeLocking.Regular.Slackness

/-! The regular locking potential uses the literal lag symbol and weights. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem symbol_zero_of_oscillation_zero (q : General.Tuning) (s : ℝ)
    (n : I → ℤ) (a : I → ℝ) (ha : ∀ i, 0 < a i) (ω : Frequency)
    (hP : oscillation n a ω = 0) : symbol q s n a 0 ω = 0 := by
  have hterms : ∀ i, a i*(1-Real.cos ((n i:ℝ)*(ω:ℝ)))=0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (ha i).le (sub_nonneg.mpr (Real.cos_le_one _)))).mp hP i (Finset.mem_univ i)
  have hlag (i : I) : (Geometry.shiftedCurve q s).lag (n i) ω = 0 := by
    have hc : Real.cos ((n i:ℝ)*(ω:ℝ))=1 := by
      have hh := (mul_eq_zero.mp (hterms i)).resolve_left (ha i).ne'
      linarith
    have hs : Real.sin ((n i:ℝ)*(ω:ℝ))=0 := by
      nlinarith [Real.sin_sq_add_cos_sq ((n i:ℝ)*(ω:ℝ))]
    rw [Curve.lag_expand, hc, hs]
    ring
  simp only [symbol, hlag, mul_zero, Finset.sum_const_zero, zero_mul, add_zero]

variable {q : General.Tuning} {t : ℝ} {L : ℕ}

def regularPotential (D : RegularData q t L) (ω : Frequency) : ℝ :=
  -finiteSymbol q t D.lags D.dual ω /
    (Real.sin (Geometry.shiftedCurve q t ω)*pinningPolynomial D.lags D.dual ω)

theorem regularSymbol_eq (D : RegularData q t L) (s : ℝ) (ω : Frequency) :
    symbol q s (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0 ω =
      finiteSymbol q s D.lags D.dual ω := by
  rw [finiteSymbol_actual]
  simp only [symbol, zero_mul, add_zero]
  exact Finset.sum_coe_sort D.lags (fun n => D.dual n * (Geometry.shiftedCurve q s).lag n ω)

theorem regularOscillation_eq (D : RegularData q t L) (ω : Frequency) :
    oscillation (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) ω =
      pinningPolynomial D.lags D.dual ω := by
  exact Finset.sum_coe_sort D.lags (fun n => D.dual n*(1-Real.cos ((n:ℝ)*(ω:ℝ))))

theorem regular_pinning_pos (D : RegularData q t L) (ω : Frequency)
    (hω : 0 < (ω:ℝ)) : 0 < pinningPolynomial D.lags D.dual ω := by
  have hnonneg : 0 ≤ pinningPolynomial D.lags D.dual ω := by
    rw [← regularOscillation_eq D ω]
    exact oscillation_nonneg (fun i : {n // n ∈ D.lags} => i.val)
      (fun i => D.dual i) (fun i => (D.dual_pos i i.property).le) ω
  by_contra hn
  have hz : pinningPolynomial D.lags D.dual ω = 0 := by linarith
  have hs := symbol_zero_of_oscillation_zero q t
    (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i)
    (fun i => D.dual_pos i i.property) ω (by rw [regularOscillation_eq D ω,hz])
  rw [regularSymbol_eq D t ω] at hs
  by_cases hatom : ∃ i, (ω:ℝ)=(D.atoms i:ℝ)
  · obtain ⟨i,hi⟩ := hatom
    have hp := D.pinning_pos i
    rw [← hi,hz] at hp
    exact lt_irrefl _ hp
  · have hd := D.dual_strict ω hω ω.property.2 (by simpa only [not_exists] using hatom)
    linarith

theorem regularPotential_zero (D : RegularData q t L) (i : Fin D.d) :
    regularPotential D (D.atoms i) = 0 := by
  rw [regularPotential,D.symbol_zero_support i,neg_zero,zero_div]

theorem regularPotential_pos (D : RegularData q t L) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) (hS : ∀ i, ω ≠ D.atoms i) :
    0 < regularPotential D ω := by
  apply div_pos
  · exact neg_pos.mpr (D.dual_strict ω hω.1 ω.property.2 (fun i he => hS i (Subtype.ext he)))
  · exact mul_pos (phase_sin_pos q t ω hω) (regular_pinning_pos D ω hω.1)

theorem regularPotential_nonneg (D : RegularData q t L) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) : 0 ≤ regularPotential D ω := by
  apply div_nonneg
  · exact neg_nonneg.mpr (D.symbol_nonpos ω ω.property)
  · exact (mul_pos (phase_sin_pos q t ω hω) (regular_pinning_pos D ω hω.1)).le

theorem continuousOn_regularPotential (D : RegularData q t L) :
    ContinuousOn (regularPotential D) Threshold.interiorCarrier := by
  have hsym : Continuous (fun ω : Frequency => finiteSymbol q t D.lags D.dual ω) := by
    have hh := continuous_symbol q t (fun i : {n // n ∈ D.lags} => i.val)
      (fun i => D.dual i) 0
    change Continuous (fun ω => symbol q t
      (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0 ω) at hh
    simpa only [regularSymbol_eq D] using hh
  have hP : Continuous (fun ω : Frequency => pinningPolynomial D.lags D.dual ω) := by
    have hh := continuous_oscillation (fun i : {n // n ∈ D.lags} => i.val)
      (fun i => D.dual i)
    change Continuous (fun ω => oscillation
      (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) ω) at hh
    simpa only [regularOscillation_eq D] using hh
  exact hsym.neg.continuousOn.div
    (((Real.continuous_sin.comp (Geometry.shiftedCurve q t).continuous).mul hP).continuousOn)
    (fun ω hω => (mul_pos (phase_sin_pos q t ω hω) (regular_pinning_pos D ω hω.1)).ne')

end polyak.ModeLocking.Localization
