import polyak.ModeLocking.Regular.Kernel

/-! The support statement is an equality of measures with the literal atom
masses. No finite-support restriction is imposed on the incoming measure. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels MeasureTheory
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def atomMasses (w : Measure Frequency) : Fin D.d → NNReal :=
  fun i => (w {D.atoms i}).toNNReal

def zeroMass (w : Measure Frequency) : NNReal := (w {frequencyZero}).toNNReal

theorem atoms_ne_zero (i : Fin D.d) : D.atoms i ≠ frequencyZero := by
  intro hi
  have hpos := (D.atoms_grid i).1
  simp only [hi, frequencyZero] at hpos
  exact lt_irrefl 0 hpos

theorem measure_decomposition {w : Measure Frequency} [IsFiniteMeasure w]
    (hcar : ∀ᵐ ω ∂w, ω = frequencyZero ∨ ∃ i, ω = D.atoms i) :
    w = atomicMeasure (D.atomMasses w) D.atoms +
      (zeroMass w : ENNReal) • Measure.dirac frequencyZero := by
  classical
  let A := Finset.univ.image D.atoms
  have h0 : frequencyZero ∉ A := by
    simp only [A, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i hi => D.atoms_ne_zero i hi
  have he : w = ∑ x ∈ insert frequencyZero A, w {x} • Measure.dirac x := by
    apply Measure.ae_mem_finset_iff.mp
    filter_upwards [hcar] with ω hω
    rcases hω with rfl | ⟨i, rfl⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [Finset.sum_insert h0, Finset.sum_image (by exact fun i _ j _ hij => D.atoms_injective hij)] at he
  calc
    w = w {frequencyZero} • Measure.dirac frequencyZero + ∑ i, w {D.atoms i} • Measure.dirac (D.atoms i) := he
    _ = _ := by
      rw [add_comm]
      simp only [atomicMeasure, atomMasses, zeroMass, ENNReal.coe_toNNReal (measure_ne_top _ _)]

theorem integral_decomposition {w : Measure Frequency} [IsFiniteMeasure w]
    (hcar : ∀ᵐ ω ∂w, ω = frequencyZero ∨ ∃ i, ω = D.atoms i)
    (f : C(Frequency, ℝ)) : (∫ ω, f ω ∂w) =
      (∑ i, (D.atomMasses w i : ℝ) * f (D.atoms i)) + (zeroMass w : ℝ) * f frequencyZero := by
  let : IsFiniteMeasure ((zeroMass w : ENNReal) • Measure.dirac frequencyZero) := by
    constructor
    simp
  conv_lhs => rw [D.measure_decomposition hcar]
  rw [integral_add_measure (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace f))
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)),
    atomicMeasure_integral, integral_smul_measure, integral_dirac]
  simp only [ENNReal.coe_toReal, smul_eq_mul]

theorem measure_kernel {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N')
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) N' w) :
    D.matrix.mulVec (fun i => (D.atomMasses w i : ℝ)) = 0 := by
  let : IsFiniteMeasure w := hw.1
  have hcar := D.program_carried hN hw
  funext r
  obtain ⟨n, hn, _, _, _, hr, _⟩ := D.class_pair r
  have ht := D.program_tight hN hw n hn
  have he : (∫ ω, (Geometry.shiftedCurve q s).lag n ω ∂w) =
      ∫ ω, (Geometry.shiftedCurve q s).lag (D.reps r) ω ∂w := by
    apply integral_congr_ae
    filter_upwards [hcar] with ω hω
    rcases hω with rfl | ⟨i, rfl⟩
    · simp only [Curve.lag_at_zero]
    · rw [lag_mod_grid (Geometry.shiftedCurve q s) (D.atoms_grid i) n, hr]
  rw [he] at ht
  have hdec := D.integral_decomposition hcar
    ⟨_, (Geometry.shiftedCurve q s).continuous_lag (D.reps r)⟩
  change (∫ ω, (Geometry.shiftedCurve q s).lag (D.reps r) ω ∂w) =
    (∑ i, (D.atomMasses w i : ℝ) * (Geometry.shiftedCurve q s).lag (D.reps r) (D.atoms i)) +
      (zeroMass w : ℝ) * (Geometry.shiftedCurve q s).lag (D.reps r) frequencyZero at hdec
  rw [hdec] at ht
  simpa only [matrix, Matrix.mulVec, dotProduct, Pi.zero_apply,
    Curve.lag_at_zero, mul_zero, zero_mul, add_zero, mul_comm] using ht

end polyak.ModeLocking.RegularData
