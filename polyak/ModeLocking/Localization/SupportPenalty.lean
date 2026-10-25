import polyak.ModeLocking.Localization.LockingAverage

/-! Every lower bound for the potential on the actual support penalizes the
shift of an arbitrary feasible measure. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
variable {q : General.Tuning} {t : ℝ} {L : ℕ}

theorem budget_integral_interior (D : RegularData q t L) (s : ℝ)
    (w : Measure Frequency) [IsFiniteMeasure w] :
    (∫ ω, regularBudget D s ω ∂w) =
      ∫ ω in Threshold.interiorCarrier, regularBudget D s ω ∂w := by
  have hi : Integrable (regularBudget D s) w :=
    (continuous_budget q s (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_endpoints_decomposition hi]
  have hz : regularBudget D s frequencyZero = 0 := by
    unfold regularBudget budget
    rw [(Geometry.shiftedCurve q s).at_zero, Real.sin_pi,zero_mul]
  have hp : regularBudget D s frequencyPi = 0 := by
    unfold regularBudget budget
    rw [(Geometry.shiftedCurve q s).at_pi, Real.sin_pi,zero_mul]
  rw [hz,hp,mul_zero,mul_zero,add_zero,add_zero]

theorem weightedPotential_integrable (D : RegularData q t L) (s : ℝ)
    (w : Measure Frequency) [IsFiniteMeasure w] :
    Integrable (fun ω => regularBudget D s ω*regularPotential D ω)
      (w.restrict Threshold.interiorCarrier) := by
  have hi : Integrable
      (defect q s t (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0) w :=
    (continuous_defect q s t _ _ 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply hi.restrict.congr
  filter_upwards [ae_restrict_mem Threshold.measurableSet_interiorCarrier] with ω hω
  exact (weightedPotential_eq_defect D s ω hω).symm

theorem support_potential_penalty (D : RegularData q t L) (s r : ℝ)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w)
    (hr : ∀ ω ∈ w.support, ω ∈ Threshold.interiorCarrier → r ≤ regularPotential D ω) :
    r ≤ s-t := by
  have : IsFiniteMeasure w := hw.1
  have hB : Integrable (regularBudget D s) w :=
    (continuous_budget q s (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm := integral_mono_ae (hB.restrict.const_mul r)
    (weightedPotential_integrable D s w) (show ∀ᵐ ω ∂w.restrict Threshold.interiorCarrier,
      r*regularBudget D s ω ≤ regularBudget D s ω*regularPotential D ω from by
        filter_upwards [ae_restrict_mem Threshold.measurableSet_interiorCarrier,
          ae_restrict_of_ae w.support_mem_ae] with ω hω hs
        nlinarith [regularBudget_nonneg D s ω,hr ω hs hω])
  rw [integral_const_mul, ← budget_integral_interior D s w] at hm
  have hpos := regularBudget_integral_pos D s hw
  have havg := regular_average_locking D s hw
  have hravg : r ≤ (∫ ω in Threshold.interiorCarrier,
      regularBudget D s ω*regularPotential D ω ∂w)/(∫ ω,regularBudget D s ω ∂w) :=
    (le_div_iff₀ hpos).mpr hm
  exact hravg.trans havg

theorem potential_inf_le_average (D : RegularData q t L) (s : ℝ)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w) :
    sInf (regularPotential D '' (w.support ∩ Threshold.interiorCarrier)) ≤
      (∫ ω in Threshold.interiorCarrier, regularBudget D s ω*regularPotential D ω ∂w) /
        (∫ ω, regularBudget D s ω ∂w) := by
  have : IsFiniteMeasure w := hw.1
  let r := sInf (regularPotential D '' (w.support ∩ Threshold.interiorCarrier))
  have hbb : BddBelow (regularPotential D '' (w.support ∩ Threshold.interiorCarrier)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨ω,hω,rfl⟩
    exact regularPotential_nonneg D ω hω.2
  have hr (ω : Frequency) (hω : ω ∈ w.support ∩ Threshold.interiorCarrier) :
      r ≤ regularPotential D ω := csInf_le hbb (mem_image_of_mem _ hω)
  have hB : Integrable (regularBudget D s) w :=
    (continuous_budget q s (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm := integral_mono_ae (hB.restrict.const_mul r)
    (weightedPotential_integrable D s w) (show ∀ᵐ ω ∂w.restrict Threshold.interiorCarrier,
      r*regularBudget D s ω ≤ regularBudget D s ω*regularPotential D ω from by
        filter_upwards [ae_restrict_mem Threshold.measurableSet_interiorCarrier,
          ae_restrict_of_ae w.support_mem_ae] with ω hω hs
        nlinarith [regularBudget_nonneg D s ω,hr ω ⟨hs,hω⟩])
  rw [integral_const_mul, ← budget_integral_interior D s w] at hm
  exact (le_div_iff₀ (regularBudget_integral_pos D s hw)).mpr hm

end polyak.ModeLocking.Localization
