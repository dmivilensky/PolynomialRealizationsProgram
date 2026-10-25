import polyak.Farey.Positions.Classes
import polyak.ModeLocking.Regular.Threshold

/-! The literal shift that places a reduced Farey harmonic on phase index one.
The inverse residue remains a signed integer, as do all certificate lags. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels Set
open scoped BigOperators

def shift (q : Tuning) (k : ℕ) (ω : ℝ) : ℝ :=
  Real.cos (Real.pi / k) / Real.sin (Real.pi / k) - Geometry.cotangent q ω

theorem phase_at_shift (q : Tuning) {k : ℕ} (hk : 3 ≤ k)
    {ω : ℝ} (hω : ω ∈ Ioo 0 Real.pi) :
    Geometry.shiftedAngle q (shift q k ω) ω = Real.pi / k := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hphase : Real.pi / k ∈ Ioo 0 Real.pi :=
    ⟨by positivity, (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr
      (by nlinarith [Real.pi_pos])⟩
  apply Geometry.angle_eq_of_cot_eq (Geometry.shiftedAngle_mem q _ hω) hphase
  rw [Geometry.cot_shiftedAngle q _ hω]
  simp only [shift, Geometry.cotangent]
  ring

def atom (j k : ℕ) (hk : 0 < k) (hjk : 2 * j ≤ k) : Frequency :=
  Farey.gridFrequency k j (by exact_mod_cast hk) (by positivity) (by exact_mod_cast hjk)

theorem atom_pos {j k : ℕ} (hj : 1 ≤ j) (hk : 0 < k) (hjk : 2 * j ≤ k) :
    0 < (atom j k hk hjk : ℝ) := by
  change 0 < 2 * Real.pi * j / k
  positivity

theorem atom_lt_pi {j k : ℕ} (hk : 0 < k) (hjk : 2 * j < k) :
    (atom j k hk hjk.le : ℝ) < Real.pi := by
  change 2 * Real.pi * j / k < Real.pi
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hjkr : (2 : ℝ) * j < k := by exact_mod_cast hjk
  exact (div_lt_iff₀ hkr).mpr (by nlinarith [Real.pi_pos])

theorem atom_grid {j k : ℕ} (hj : 1 ≤ j) (hk : 0 < k) (hjk : 2 * j ≤ k) :
    atom j k hk hjk ∈ periodicGrid k := by
  refine ⟨atom_pos hj hk hjk, (j : ℤ), ?_⟩
  change (k : ℝ) * (2 * Real.pi * j / k) = (j : ℝ) * (2 * Real.pi)
  field_simp

theorem phase_index_one {j k : ℕ} (hk : 0 < k) (hjk : 2 * j ≤ k)
    (Θ : Curve) (hphase : Θ (atom j k hk hjk) = Real.pi / k) :
    Farey.gridPhase Θ k j (by exact_mod_cast hk) (by positivity)
      (by exact_mod_cast hjk) = 1 := by
  unfold Farey.gridPhase
  change (k : ℝ) * Θ (atom j k hk hjk) / Real.pi = 1
  rw [hphase]
  field_simp

theorem lag_position_one {j k : ℕ} (hk : 0 < k) (hjk : 2 * j ≤ k)
    (Θ : Curve) (hphase : Θ (atom j k hk hjk) = Real.pi / k) (n : ℤ) :
    Θ.lag n (atom j k hk hjk) = Farey.positionValue k 1 (((n * j) % k : ℤ) : ℝ) := by
  rw [atom, Farey.lag_at_grid_eq_positionValue, phase_index_one hk hjk Θ hphase]

theorem residue_one_iff {j k : ℕ} (hk : 0 < k) {b r : ℤ}
    (hb : b * (j : ℤ) ≡ 1 [ZMOD (k : ℤ)]) (hb0 : 0 < b) (hbk : b < k)
    (hr0 : 0 ≤ r) (hrk : r < k) :
    (r * j) % k = 1 ↔ r = b := by
  constructor
  · intro h
    have he := Farey.residue_transport_of_inverse (i := 1) hb r
    simp only [mul_one, one_mul, h, Int.emod_eq_of_lt hr0 hrk,
      Int.emod_eq_of_lt hb0.le hbk] at he
    exact he
  · rintro rfl
    simpa only [Int.ModEq, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 1)
      (by omega : (1 : ℤ) < k)] using hb

theorem lag_trig_reduce {j k : ℕ} (hk : 0 < k) (hjk : 2 * j ≤ k)
    (n : ℤ) (θ : ℝ) :
    Real.cos ((n : ℝ) * (atom j k hk hjk : ℝ) - θ) =
      Real.cos (2 * Real.pi * (((n * j) % k : ℤ) : ℝ) / k - θ) ∧
    Real.sin ((n : ℝ) * (atom j k hk hjk : ℝ) - θ) =
      Real.sin (2 * Real.pi * (((n * j) % k : ℤ) : ℝ) / k - θ) := by
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : (n : ℝ) * (atom j k hk hjk : ℝ) - θ =
      (2 * Real.pi * (((n * j) % k : ℤ) : ℝ) / k - θ) +
        (((n * j) / k : ℤ) : ℝ) * (2 * Real.pi) := by
    change (n : ℝ) * (2 * Real.pi * j / k) - θ = _
    have he := Int.emod_add_ediv_mul (n * j) k
    have her : (((n * j) % k : ℤ) : ℝ) + (((n * j) / k : ℤ) : ℝ) * k =
        (n : ℝ) * j := by exact_mod_cast he
    field_simp
    linear_combination -2 * Real.pi * her
  rw [he, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  exact ⟨rfl, rfl⟩

end polyak.FareyPlateau.Edge
