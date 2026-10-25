import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-! The fan-period congruence has arbitrarily large solutions precisely for
coprime period and window index. There is no finite search over p. -/
namespace polyak.ModeLocking.Periods

theorem exists_fan_period_iff {L K : ℕ} (hL : 0 < L) :
    (∃ p : ℕ, 2 ≤ p ∧ L ∣ p * K + 1) ↔ L.Coprime K := by
  constructor
  · rintro ⟨p, _, hp⟩
    have hh : K.Coprime (p * K + 1) := by simp
    exact (Nat.Coprime.of_dvd_right hp hh).symm
  · intro hcop
    by_cases hone : L = 1
    · exact ⟨2, le_rfl, by simp [hone]⟩
    have hLgt : 1 < L := by omega
    obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_of_coprime (L - 1) hcop.symm hL.ne'
    refine ⟨m + 2 * L, by omega, ?_⟩
    have hbase : L ∣ m * K + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, Nat.mul_comm m K, hm]
      have hmod : (L - 1) % L = L - 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      rw [Nat.mod_eq_of_lt hLgt]
      have hsub : L - 1 + 1 = L := by omega
      rw [hsub, Nat.mod_self]
    have hextra : L ∣ 2 * L * K := by
      exact dvd_mul_of_dvd_left (dvd_mul_left L 2) K
    convert Nat.dvd_add hbase hextra using 1
    ring

theorem arbitrarily_large_fan_periods {L K : ℕ} (hL : 0 < L) (hc : L.Coprime K)
    (B : ℕ) : ∃ p : ℕ, B ≤ p ∧ 2 ≤ p ∧ L ∣ p * K + 1 := by
  obtain ⟨p, hp, hd⟩ := exists_fan_period_iff hL |>.mpr hc
  refine ⟨p + B * L, by nlinarith, by omega, ?_⟩
  have he : L ∣ B * L * K := dvd_mul_of_dvd_left (dvd_mul_left L B) K
  convert Nat.dvd_add hd he using 1
  ring

end polyak.ModeLocking.Periods
