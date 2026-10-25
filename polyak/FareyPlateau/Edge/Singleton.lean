import polyak.FareyPlateau.Edge.Persistence

/-! A regular singleton regime at a reduced Farey frequency must lie on
the exact phase-one tongue edge. The regular certificate may have any period. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking Set MeasureTheory
open scoped BigOperators

theorem singleton_phase_eq {q : Tuning} {s : ℝ} {L j k : ℕ}
    (D : RegularData q s L) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : 2 * j < k)
    (b : ℤ) (hb : (b * j) % k = 1)
    (hS : Set.range D.atoms = {atom j k (by omega) hjk.le}) :
    Geometry.shiftedCurve q s (atom j k (by omega) hjk.le) = Real.pi / k := by
  let ω := atom j k (by omega) hjk.le
  let Θ := Geometry.shiftedCurve q s
  have hatom (i : Fin D.d) : D.atoms i = ω := by
    have hi : D.atoms i ∈ ({ω} : Set Frequency) := by rw [← hS]; exact ⟨i, rfl⟩
    exact Set.mem_singleton_iff.mp hi
  have hsum : ∑ i, (D.primal i : ℝ) = 1 := by exact_mod_cast D.primal_sum
  have hlag (n : ℤ) : 0 ≤ Θ.lag n ω := by
    by_cases hn : n = 0
    · simp only [hn, Curve.lag_zero, le_refl]
    have hh := D.primal_feasible.2.2.2 n hn
    rw [RegularData.measure, atomicMeasure_integral] at hh
    simp only [hatom, ← Finset.sum_mul, hsum, one_mul] at hh
    exact hh
  have htight (n : ℤ) (hn : n ∈ D.lags) : Θ.lag n ω = 0 := by
    have hh := D.lag_tight n hn
    simpa only [hatom, ← Finset.sum_mul, hsum, one_mul] using hh
  let a := Farey.gridPhase Θ k j (by omega) (by positivity) (by exact_mod_cast hjk.le)
  have ha0 : 0 < a := Farey.gridPhase_pos Θ k j (by omega) (by positivity) (by exact_mod_cast hjk.le)
  have hak : a ≤ k := Farey.gridPhase_le Θ k j (by omega) (by positivity) (by exact_mod_cast hjk.le)
  have hkZ : (0 : ℤ) < k := by omega
  have ha1 : a ≤ 1 := by
    have hh := hlag b
    change 0 ≤ Θ.lag b (Farey.gridFrequency k j (by omega) (by positivity) (by exact_mod_cast hjk.le)) at hh
    rw [Farey.lag_at_grid_eq_positionValue, hb] at hh
    apply (Farey.positionValue_nonneg_iff hkZ ha0 hak (by norm_num) (by exact_mod_cast (show 1 < k by omega))).mp
    simpa only [Int.cast_one] using hh
  let i : Fin D.d := ⟨0, D.d_pos⟩
  have hpin : 0 < pinningPolynomial D.lags D.dual ω := by
    simpa only [hatom] using D.pinning_pos i
  obtain ⟨n, hn, hncos⟩ : ∃ n ∈ D.lags, Real.cos ((n : ℝ) * (ω : ℝ)) ≠ 1 := by
    by_contra hn
    have hcos : ∀ n ∈ D.lags, Real.cos ((n : ℝ) * (ω : ℝ)) = 1 := by
      simpa only [not_exists, not_and, not_not] using hn
    have he : pinningPolynomial D.lags D.dual ω = 0 := by
      unfold pinningPolynomial
      apply Finset.sum_eq_zero
      intro n hn
      rw [hcos n hn]
      ring
    linarith
  have hρ0 : (n * j) % k ≠ 0 := by
    intro hz
    have hh := (lag_trig_reduce (by omega) hjk.le n 0).1
    simp only [hz, Int.cast_zero, mul_zero, zero_div, sub_zero, Real.cos_zero] at hh
    exact hncos hh
  have hρpos : 0 < (n * j) % k := by
    have hh := Int.emod_nonneg (n * j) hkZ.ne'
    omega
  have heq : (((n * j) % k : ℤ) : ℝ) = a := by
    have hh := htight n hn
    change Θ.lag n (Farey.gridFrequency k j (by omega) (by positivity) (by exact_mod_cast hjk.le)) = 0 at hh
    rw [Farey.lag_at_grid_eq_positionValue] at hh
    exact (Farey.positionValue_eq_zero_iff hkZ ha0 hak (by exact_mod_cast hρpos)
      (by exact_mod_cast Int.emod_lt_of_pos (n * j) hkZ)).mp hh
  have haeq : a = 1 := by
    have hρone : (1 : ℝ) ≤ ((n * j) % k : ℤ) := by exact_mod_cast (show 1 ≤ (n * j) % k by omega)
    linarith
  change (k : ℝ) * Θ ω / Real.pi = 1 at haeq
  have he : (k : ℝ) * Θ ω = Real.pi := by
    have hh := (div_eq_iff Real.pi_ne_zero).mp haeq
    simpa only [one_mul] using hh
  exact (eq_div_iff (by positivity : (k : ℝ) ≠ 0)).mpr (by nlinarith)

theorem singleton_shift_eq {q : Tuning} {s : ℝ} {L j k : ℕ}
    (D : RegularData q s L) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : 2 * j < k)
    (b : ℤ) (hb : (b * j) % k = 1)
    (hS : Set.range D.atoms = {atom j k (by omega) hjk.le}) :
    s = shift q k (atom j k (by omega) hjk.le) := by
  have hp := singleton_phase_eq D hk hj hjk b hb hS
  have hc := Geometry.cot_shiftedAngle q s
    ⟨atom_pos hj (by omega) hjk.le, atom_lt_pi (by omega) hjk⟩
  change Geometry.shiftedAngle q s (atom j k (by omega) hjk.le) = _ at hp
  rw [hp] at hc
  unfold shift Geometry.cotangent
  linarith

end polyak.FareyPlateau.Edge
