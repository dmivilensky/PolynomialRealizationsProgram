import polyak.FareyPlateau.Edge.Certificate
import polyak.ModeLocking.Regular.Persistence
import polyak.ModeLocking.Regular.Uniqueness

/-! The certificate gives the literal edge shift throughout a neighborhood,
not merely a nearby unnamed analytic threshold branch. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking Set Filter MeasureTheory
open scoped BigOperators Topology

theorem shift_eq_of_tight {j k : ℕ} (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : 2 * j < k)
    (q : Tuning) (s : ℝ) (b : ℤ) (hb : (b * j) % k = 1)
    (htight : (Geometry.shiftedCurve q s).lag b (atom j k (by omega) hjk.le) = 0) :
    s = shift q k (atom j k (by omega) hjk.le) := by
  let ω := atom j k (by omega) hjk.le
  have hω : (ω : ℝ) ∈ Ioo 0 Real.pi := ⟨atom_pos hj (by omega) hjk.le, atom_lt_pi (by omega) hjk⟩
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : Real.pi / k ∈ Ioo 0 Real.pi := ⟨by positivity,
    (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos])⟩
  have hphase := Geometry.shiftedAngle_mem q s hω
  have hl : 2 * Real.sin (Real.pi / k) *
      Real.sin (Real.pi / k - Geometry.shiftedAngle q s ω) = 0 := by
    change Real.cos (Geometry.shiftedAngle q s ω) -
      Real.cos ((b : ℝ) * (ω : ℝ) - Geometry.shiftedAngle q s ω) = 0 at htight
    rw [(lag_trig_reduce (by omega) hjk.le b (Geometry.shiftedAngle q s ω)).1, hb] at htight
    have hval := Lattice.lagValue_eq_sines (Geometry.shiftedAngle q s ω) (2 * Real.pi / k)
    unfold Lattice.lagValue at hval
    simp only [Int.cast_one, mul_one] at htight
    rw [hval] at htight
    have hhalf : 2 * Real.pi / (k : ℝ) / 2 = Real.pi / k := by ring
    simpa only [hhalf] using htight
  have hs := Real.sin_pos_of_pos_of_lt_pi hc.1 hc.2
  have hz : Real.sin (Real.pi / k - Geometry.shiftedAngle q s ω) = 0 :=
    (mul_eq_zero.mp hl).resolve_left (mul_pos (by norm_num) hs).ne'
  have he := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hphase.2, hc.1]) (by linarith [hphase.1, hc.2])).mp hz
  have hcoteq := Geometry.cot_shiftedAngle q s hω
  rw [show Geometry.shiftedAngle q s ω = Real.pi / k by linarith] at hcoteq
  unfold shift
  change s = _ - Geometry.cotangent q ω
  unfold Geometry.cotangent
  linarith

namespace Certificate
variable {q : Tuning} {s : ℝ} {j k : ℕ} (C : Certificate q s j k)

include C in
theorem sigma_eq_shift_near : ∀ᶠ q' in 𝓝 q,
    Threshold.sigma q' = shift q' k C.frequency := by
  filter_upwards [C.regularData.regular_persistence] with q' hq'
  obtain ⟨D', ha, hr, _hN⟩ := hq'
  have hatom (i : Fin D'.d) : D'.atoms i = C.frequency := by
    have hi : D'.atoms i ∈ Set.range C.regularData.atoms := by rw [← ha]; exact ⟨i, rfl⟩
    obtain ⟨r, he⟩ := hi
    exact he.symm
  have hrep (i : Fin D'.d) : D'.reps i = C.inverse := by
    have hi : D'.reps i ∈ Set.range C.regularData.reps := by rw [← hr]; exact ⟨i, rfl⟩
    obtain ⟨r, he⟩ := hi
    exact he.symm
  let i : Fin D'.d := ⟨0, D'.d_pos⟩
  have ht := D'.tight i
  simp only [hatom, hrep, ← Finset.sum_mul] at ht
  have hsum : ∑ r, (D'.primal r : ℝ) = 1 := by exact_mod_cast D'.primal_sum
  rw [hsum, one_mul] at ht
  apply shift_eq_of_tight C.period_ge C.numerator_pos C.numerator_lt q' _ C.inverse _ ht
  simpa only [Int.ModEq, Int.emod_eq_of_lt (by have := C.period_ge; omega : (0 : ℤ) ≤ 1)
    (by have := C.period_ge; omega : (1 : ℤ) < k)] using C.inverse_mod

theorem measure_eq_dirac : C.regularData.measure = Measure.dirac C.frequency := by
  change (∑ _i : Fin 1, (1 : ENNReal) • Measure.dirac C.frequency) = _
  simp

theorem extremal_classification {w : Measure Frequency}
    (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w) :
    ∃ b a : NNReal, 0 < b ∧
      w = (b : ENNReal) • Measure.dirac C.frequency +
        (a : ENNReal) • Measure.dirac frequencyZero ∧
      (a : ℝ) ≤ (b : ℝ) * Real.cos (Real.pi / k) := by
  obtain ⟨b, a, hb, he, ha⟩ := C.regularData.extremal_classification
    (fun n hn => C.nonzero n hn) hw
  refine ⟨b, a, hb, ?_, ?_⟩
  · simpa only [C.measure_eq_dirac] using he
  · rw [C.measure_eq_dirac, integral_dirac] at ha
    change (a : ℝ) ≤ (b : ℝ) * Real.cos (Geometry.shiftedCurve q s C.frequency) at ha
    simpa only [show Geometry.shiftedCurve q s C.frequency = Real.pi / k from C.phase] using ha

include C in
theorem certjk_near : ∀ᶠ q' in 𝓝 q,
    Threshold.sigma q' = shift q' k C.frequency ∧
    Threshold.sigmaPeriodic q' k = shift q' k C.frequency ∧
    RegularPoint q' (shift q' k C.frequency) k ∧
    ∀ w : Measure Frequency,
      ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) nonzeroLags w →
      ∃ b a : NNReal, 0 < b ∧
        w = (b : ENNReal) • Measure.dirac C.frequency +
          (a : ENNReal) • Measure.dirac frequencyZero ∧
        (a : ℝ) ≤ (b : ℝ) * Real.cos (Real.pi / k) := by
  filter_upwards [C.regularData.regular_persistence, C.sigma_eq_shift_near] with q' hq' hs
  obtain ⟨D', hS, _hr, _hN⟩ := hq'
  have hatom (i : Fin D'.d) : D'.atoms i = C.frequency := by
    have hi : D'.atoms i ∈ Set.range C.regularData.atoms := by rw [← hS]; exact ⟨i, rfl⟩
    obtain ⟨r, he⟩ := hi
    exact he.symm
  have hm : D'.measure = Measure.dirac C.frequency := by
    unfold RegularData.measure atomicMeasure
    simp only [hatom, ← Finset.sum_smul, ← ENNReal.ofNNReal_finsetSum,
      D'.primal_sum, ENNReal.coe_one, one_smul]
  have hp : Geometry.shiftedCurve q' (Threshold.sigma q') C.frequency = Real.pi / k := by
    rw [hs]
    exact phase_at_shift q' C.period_ge
      ⟨atom_pos C.numerator_pos (by have := C.period_ge; omega) C.numerator_lt.le,
        atom_lt_pi (by have := C.period_ge; omega) C.numerator_lt⟩
  refine ⟨hs, D'.sigmaPeriodic_eq.trans hs, ?_, ?_⟩
  · rw [← hs]
    exact ⟨D'⟩
  · intro w hw
    obtain ⟨b, a, hb, he, ha⟩ := D'.extremal_classification (fun n hn => D'.lags_nonzero n hn) hw
    refine ⟨b, a, hb, ?_, ?_⟩
    · simpa only [hm] using he
    · rw [hm, integral_dirac] at ha
      change (a : ℝ) ≤ (b : ℝ) * Real.cos (Geometry.shiftedCurve q' (Threshold.sigma q') C.frequency) at ha
      simpa only [hp] using ha

end Certificate
end polyak.FareyPlateau.Edge
