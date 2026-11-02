import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Article: main_krylov, apC:lem:fund, partition background.
Use: genuine equal time partitions with arbitrarily small mesh. The sequence
is held constant after its last point, so it is monotone on all natural indices.
Source: the Archimedean property of the real numbers.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set

def equalGrid (a b : ℝ) (N i : ℕ) : ℝ :=
  a + (b - a) * (min i N : ℕ) / N

theorem equalGrid_zero (a b : ℝ) (N : ℕ) : equalGrid a b N 0 = a := by
  simp [equalGrid]

theorem equalGrid_end (a b : ℝ) {N : ℕ} (hN : 0 < N) : equalGrid a b N N = b := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [equalGrid, min_self]
  field_simp
  ring

theorem equalGrid_mono {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    Monotone (equalGrid a b N) := by
  intro i j hij
  unfold equalGrid
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
  exact_mod_cast min_le_min_right N hij

theorem equalGrid_mem {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N) (i : ℕ) :
    equalGrid a b N i ∈ Icc a b := by
  have hlo := equalGrid_mono hab N (Nat.zero_le i)
  have hlast : equalGrid a b N i ≤ equalGrid a b N N := by
    unfold equalGrid
    simp only [min_self]
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
    exact_mod_cast min_le_right i N
  exact ⟨by simpa only [equalGrid_zero] using hlo,
    by simpa only [equalGrid_end a b hN] using hlast⟩

theorem equalGrid_step {a b : ℝ} {N i : ℕ} (hi : i < N) :
    equalGrid a b N (i + 1) - equalGrid a b N i = (b - a) / N := by
  simp only [equalGrid, min_eq_left (Nat.succ_le_of_lt hi), min_eq_left hi.le,
    Nat.cast_succ]
  ring

/-- Every positive mesh tolerance admits an actual equal partition. -/
theorem exists_equalGrid {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ Monotone (equalGrid a b N) ∧
      equalGrid a b N 0 = a ∧ equalGrid a b N N = b ∧
      (∀ i, equalGrid a b N i ∈ Icc a b) ∧
      ∀ i < N, equalGrid a b N (i + 1) - equalGrid a b N i < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((b - a) / δ))
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hN)
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  refine ⟨N, hNpos, equalGrid_mono hab N, equalGrid_zero a b N,
    equalGrid_end a b hNpos, equalGrid_mem hab hNpos, ?_⟩
  intro i hi
  rw [equalGrid_step hi]
  apply (div_lt_iff₀ hNr).mpr
  have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hN)
  nlinarith

end
end krylov.ContinuumBV
