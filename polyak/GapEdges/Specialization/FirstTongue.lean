import polyak.FareyPlateau.Edge.Basic
import polyak.Levels.Chart.BoundaryFaces
import polyak.Farey.Geometry.Localization
import polyak.Levels.Geometry.LevelZeroExclusive

/-! Exact j=1 edge equations, including the shift sign and the exclusion
of all geometric gaps from a closed first tongue. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set

theorem first_shift_nonpos_iff (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    FareyPlateau.Edge.shift q k (2 * Real.pi / k) ≤ 0 ↔
      q.angle (2 * Real.pi / k) ≤ Real.pi / k := by
  have hω := Chart.boundaryAngle_strict_mem hk
  have hsin := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  change 0 < Real.sin (2 * Real.pi / (k : ℝ)) at hsin
  have he := (Regions.rational_angle_le_iff_explicit q (j := 1)
    (by norm_num) (by omega : 2 * 1 < k)).1
  simp only [Regions.rationalAngle, Nat.cast_one, mul_one] at he
  rw [FareyPlateau.Edge.shift, sub_nonpos, Geometry.cotangent, le_div_iff₀ hsin]
  exact he.symm

theorem first_shift_pos_iff (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    0 < FareyPlateau.Edge.shift q k (2 * Real.pi / k) ↔
      Real.pi / k < q.angle (2 * Real.pi / k) := by
  simpa only [not_le] using not_congr (first_shift_nonpos_iff q hk)

theorem gap_outside_first_tongue {K k : ℕ} {q : Tuning}
    (hq : Geometry.Gap K q) (hk : 3 ≤ k) :
    Real.pi / k < q.angle (2 * Real.pi / k) := by
  apply lt_of_not_ge
  intro hphase
  have hmem : Geometry.firstFrequency k (by omega) ∈ Geometry.closedDip (tuningCurve q) := by
    change q.angle (2 * Real.pi / k) ≤ (2 * Real.pi / k) / 2
    exact hphase.trans_eq (by ring)
  exact Geometry.firstFrequency_not_in_window hq.1 hk (Farey.gap_closedDip_window hq _ hmem)

theorem first_shift_pos_in_every_gap {K k : ℕ} {q : Tuning}
    (hq : Geometry.Gap K q) (hk : 3 ≤ k) :
    0 < FareyPlateau.Edge.shift q k (2 * Real.pi / k) :=
  (first_shift_pos_iff q hk).mpr (gap_outside_first_tongue hq hk)

/-- Both explicit fan pairs straddle 1/k with the paper's ordering. -/
theorem first_fans_straddle {k m : ℕ} (hk : 3 ≤ k) (hm : 1 ≤ m) :
    (m : ℝ) / (k * m + k - 1) < 1 / k ∧
      1 / (k : ℝ) < ((m : ℝ) + 1) / (k * m + k - 1) ∧
      (m : ℝ) / (k * m + 1) < 1 / k ∧
      1 / (k : ℝ) < ((m : ℝ) + 1) / (k * m + 1) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hprod : 0 ≤ (k : ℝ) * m := mul_nonneg (by linarith) (by linarith)
  have hdm : 0 < (k : ℝ) * m + k - 1 := by linarith
  have hdp : 0 < (k : ℝ) * m + 1 := by linarith
  have hkp : 0 < (k : ℝ) := by linarith
  refine ⟨(div_lt_div_iff₀ hdm hkp).mpr ?_,
    (div_lt_div_iff₀ hkp hdm).mpr ?_,
    (div_lt_div_iff₀ hdp hkp).mpr ?_, (div_lt_div_iff₀ hkp hdp).mpr ?_⟩ <;> nlinarith

/-- An explicit common cutoff puts all four fan entries in their claimed
adjacent windows; no eventual-location premise is supplied. -/
theorem first_fans_in_adjacent_windows {k m : ℕ} (hk : 3 ≤ k) (hm : k ≤ m) :
    1 / ((k : ℝ) + 1) < (m : ℝ) / (k * m + k - 1) ∧
      (m : ℝ) / (k * m + k - 1) < 1 / k ∧
      1 / (k : ℝ) < ((m : ℝ) + 1) / (k * m + k - 1) ∧
      ((m : ℝ) + 1) / (k * m + k - 1) < 1 / ((k : ℝ) - 1) ∧
      1 / ((k : ℝ) + 1) < (m : ℝ) / (k * m + 1) ∧
      (m : ℝ) / (k * m + 1) < 1 / k ∧
      1 / (k : ℝ) < ((m : ℝ) + 1) / (k * m + 1) ∧
      ((m : ℝ) + 1) / (k * m + 1) < 1 / ((k : ℝ) - 1) := by
  obtain ⟨hs₁, hs₂, hs₃, hs₄⟩ := first_fans_straddle hk (by omega : 1 ≤ m)
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hmr : (k : ℝ) ≤ m := by exact_mod_cast hm
  have hprod : 0 ≤ (k : ℝ) * m := mul_nonneg (by linarith) (by linarith)
  have hdm : 0 < (k : ℝ) * m + k - 1 := by linarith
  have hdp : 0 < (k : ℝ) * m + 1 := by linarith
  have hp : 0 < (k : ℝ) + 1 := by linarith
  have hn : 0 < (k : ℝ) - 1 := by linarith
  refine ⟨(div_lt_div_iff₀ hp hdm).mpr ?_, hs₁, hs₂,
    (div_lt_div_iff₀ hdm hn).mpr ?_, (div_lt_div_iff₀ hp hdp).mpr ?_, hs₃, hs₄,
    (div_lt_div_iff₀ hdp hn).mpr ?_⟩ <;> nlinarith

end polyak.GapEdges
