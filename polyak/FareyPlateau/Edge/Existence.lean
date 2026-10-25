import polyak.FareyPlateau.Edge.Adjacent

/-! The adjacent-lag witnesses exist for every nonresonant slope index.
They are constructed by an integer floor, not supplied as extra premises. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking

theorem adjacent_lags_exist (b : ℤ) {k N : ℝ} (hk : 0 < k)
    (hres : ∀ m : ℤ, N ≠ (b : ℝ) + m * k) :
    ∃ m : ℤ, (b : ℝ) + m * k < N ∧ N < (b : ℝ) + ((m : ℝ) + 1) * k := by
  let m : ℤ := ⌊(N - b) / k⌋
  have hlo := Int.floor_le ((N - b) / k)
  have hhi := Int.lt_floor_add_one ((N - b) / k)
  have h₁ : (b : ℝ) + m * k ≤ N := by
    have hh := (le_div_iff₀ hk).mp hlo
    linarith
  have h₂ : N < (b : ℝ) + ((m : ℝ) + 1) * k := by
    have hh := (div_lt_iff₀ hk).mp hhi
    linarith
  exact ⟨m, lt_of_le_of_ne h₁ (Ne.symm (hres m)), h₂⟩

theorem adjacentData_nonempty (q : Tuning) {j k : ℕ} (hk : 3 ≤ k)
    (hj : 1 ≤ j) (hjk : 2 * j < k) (b : ℤ) (hb0 : 0 < b) (hbk : b < k)
    (hb : b * (j : ℤ) ≡ 1 [ZMOD (k : ℤ)])
    (hres : ∀ m : ℤ,
      2 * deriv (TwoLag.phase q (shift q k (atom j k (by omega) hjk.le)))
        (atom j k (by omega) hjk.le : ℝ) ≠ (b : ℝ) + m * k) :
    Nonempty (AdjacentData q j k) := by
  let ω := atom j k (by omega) hjk.le
  let N := 2 * deriv (TwoLag.phase q (shift q k ω)) ω
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨m, hlo, hhi⟩ := adjacent_lags_exist b hkR hres
  let n : ℤ := b + m * k
  have hn : (n : ℝ) = (b : ℝ) + m * k := by simp only [n, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  let t : ℝ := (N - n) / k
  have ht0 : 0 < t := by
    apply div_pos _ hkR
    rw [hn]
    exact sub_pos.mpr hlo
  have ht1 : t < 1 := by
    apply (div_lt_iff₀ hkR).mpr
    rw [hn]
    dsimp only [N, ω] at *
    nlinarith only [hhi]
  refine ⟨{
    period_ge := hk
    numerator_pos := hj
    numerator_lt := hjk
    inverse := b
    inverse_pos := hb0
    inverse_lt := hbk
    inverse_mod := hb
    lower := n
    lower_class := ?_
    mix := t
    mix_pos := ht0
    mix_lt := ht1
    slope := ?_ }⟩
  · change (b + m * (k : ℤ)) % k = b
    rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt hb0.le hbk]
  · change N = (n : ℝ) + ((N - n) / k) * k
    rw [div_mul_cancel₀ _ hkR.ne']
    ring

end polyak.FareyPlateau.Edge
