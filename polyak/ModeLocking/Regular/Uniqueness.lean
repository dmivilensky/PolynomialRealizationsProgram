import polyak.ModeLocking.Regular.Support

/-! The threshold extremal classification holds for every finite measure,
and for every set of constraints containing the regular finite lag set. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels MeasureTheory
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem atomicMeasure_mul {J : Type*} [Fintype J] (a : J → NNReal) (x : J → Frequency)
    (c : NNReal) : atomicMeasure (fun i => c * a i) x = (c : ENNReal) • atomicMeasure a x := by
  unfold atomicMeasure
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.coe_mul, mul_smul]

theorem extremal_classification {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N')
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) N' w) :
    ∃ c a : NNReal, 0 < c ∧
      w = (c : ENNReal) • D.measure + (a : ENNReal) • Measure.dirac frequencyZero ∧
      (a : ℝ) ≤ (c : ℝ) * ∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂D.measure := by
  let : IsFiniteMeasure w := hw.1
  have hcar := D.program_carried hN hw
  obtain ⟨c, hc⟩ := D.kernel_unique (D.measure_kernel hN hw)
  let i₀ : Fin D.d := ⟨0, D.d_pos⟩
  have hc_nonneg : 0 ≤ c := by
    have hp : 0 < (D.primal i₀ : ℝ) := by exact_mod_cast D.primal_pos i₀
    have hn := (D.atomMasses w i₀).coe_nonneg
    rw [hc i₀] at hn
    exact (mul_nonneg_iff_of_pos_right hp).mp hn
  let cn : NNReal := ⟨c, hc_nonneg⟩
  have hweights : D.atomMasses w = fun i => cn * D.primal i := by
    funext i
    apply NNReal.coe_injective
    exact hc i
  have hmeasure : w = (cn : ENNReal) • D.measure +
      (zeroMass w : ENNReal) • Measure.dirac frequencyZero := by
    calc
      w = atomicMeasure (D.atomMasses w) D.atoms + (zeroMass w : ENNReal) • Measure.dirac frequencyZero := D.measure_decomposition hcar
      _ = _ := by rw [hweights, atomicMeasure_mul]; rfl
  have hmin := D.integral_decomposition hcar
    ⟨_, (Geometry.shiftedCurve q s).continuous_minimizer⟩
  change (∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂w) =
    (∑ i, (D.atomMasses w i : ℝ) * (Geometry.shiftedCurve q s).minimizer (D.atoms i)) +
      (zeroMass w : ℝ) * (Geometry.shiftedCurve q s).minimizer frequencyZero at hmin
  simp only [Curve.minimizer_at_zero, mul_neg, mul_one] at hmin
  simp only [hc, mul_assoc, ← Finset.mul_sum] at hmin
  have hslack : (zeroMass w : ℝ) ≤ c *
      ∑ i, (D.primal i : ℝ) * (Geometry.shiftedCurve q s).minimizer (D.atoms i) := by
    linarith [hw.2.2.1]
  have hc_pos : 0 < cn := by
    apply lt_of_le_of_ne (show 0 ≤ cn from zero_le)
    intro hz
    have hcz : c = 0 := congrArg (fun t : NNReal => (t : ℝ)) hz.symm
    have haz : zeroMass w = 0 := by
      apply NNReal.coe_injective
      simp only [hcz, zero_mul] at hslack
      exact le_antisymm hslack (zeroMass w).coe_nonneg
    apply hw.2.1
    simpa only [← hz, haz, ENNReal.coe_zero, zero_smul, add_zero] using hmeasure
  refine ⟨cn, zeroMass w, hc_pos, hmeasure, ?_⟩
  change (zeroMass w : ℝ) ≤ c * ∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂D.measure
  simpa only [measure, atomicMeasure_integral] using hslack

theorem scaled_extremal_solution (c a : NNReal) (hc : 0 < c)
    (ha : (a : ℝ) ≤ (c : ℝ) * ∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂D.measure) :
    ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags
      ((c : ENNReal) • D.measure + (a : ENNReal) • Measure.dirac frequencyZero) := by
  let : IsFiniteMeasure D.measure := D.primal_feasible.1
  let : IsFiniteMeasure ((c : ENNReal) • D.measure) := D.measure.smul_finite ENNReal.coe_ne_top
  let : IsFiniteMeasure ((a : ENNReal) • Measure.dirac frequencyZero) :=
    (Measure.dirac frequencyZero).smul_finite ENNReal.coe_ne_top
  have hint (f : C(Frequency, ℝ)) :
      (∫ ω, f ω ∂((c : ENNReal) • D.measure + (a : ENNReal) • Measure.dirac frequencyZero)) =
        (c : ℝ) * (∫ ω, f ω ∂D.measure) + (a : ℝ) * f frequencyZero := by
    rw [integral_add_measure
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)),
      integral_smul_measure, integral_smul_measure, integral_dirac]
    simp only [ENNReal.coe_toReal, smul_eq_mul]
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro hz
    have hd : D.measure Set.univ = 1 := by
      simp only [measure, atomicMeasure, Measure.coe_finsetSum, Finset.sum_apply,
        Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
        ← ENNReal.ofNNReal_finsetSum, D.primal_sum, ENNReal.coe_one]
    have he := congrArg (fun μ : Measure Frequency => μ Set.univ) hz
    have hsum : (c : ENNReal) + (a : ENNReal) = 0 := by
      simpa only [Measure.add_apply, Measure.smul_apply, hd, smul_eq_mul, mul_one,
        Measure.dirac_apply_of_mem (Set.mem_univ _), Measure.coe_zero, Pi.zero_apply] using he
    exact hc.ne' (by exact_mod_cast (add_eq_zero.mp hsum).1)
  · have he := hint ⟨_, (Geometry.shiftedCurve q s).continuous_minimizer⟩
    change (∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂_) = _ at he
    change 0 ≤ ∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂_
    rw [he]
    simp only [ContinuousMap.coe_mk, Curve.minimizer_at_zero] 
    linarith
  · intro n hn
    have he := hint ⟨_, (Geometry.shiftedCurve q s).continuous_lag n⟩
    change (∫ ω, (Geometry.shiftedCurve q s).lag n ω ∂_) = _ at he
    rw [he]
    simp only [ContinuousMap.coe_mk, Curve.lag_at_zero, mul_zero, add_zero]
    simpa only [] using
      mul_nonneg c.coe_nonneg (D.primal_feasible.2.2.2 n hn)

theorem extremal_iff {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N') (hN' : N' ⊆ nonzeroLags)
    (w : Measure Frequency) : ProgramSolution (Geometry.shiftedCurve q s) N' w ↔
      ∃ c a : NNReal, 0 < c ∧
        w = (c : ENNReal) • D.measure + (a : ENNReal) • Measure.dirac frequencyZero ∧
        (a : ℝ) ≤ (c : ℝ) * ∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂D.measure := by
  refine ⟨fun hw => D.extremal_classification hN hw, ?_⟩
  rintro ⟨c, a, hc, rfl, ha⟩
  exact (D.scaled_extremal_solution c a hc ha).relax hN'

theorem exact_relaxation {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N') (hN' : N' ⊆ nonzeroLags)
    (w : Measure Frequency) : ProgramSolution (Geometry.shiftedCurve q s) N' w ↔
      ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w := by
  rw [D.extremal_iff hN hN', D.extremal_iff (N' := nonzeroLags) (fun n hn => D.lags_nonzero n hn) (fun _ h => h)]

end polyak.ModeLocking.RegularData
