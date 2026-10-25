import polyak.ModeLocking.Continuation.Kernels

/-! Exact finite partition into the nonzero tight classes and the zero
class, with signed integer quotients retained for slope moments. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem sum_classes (f : ℤ → ℝ) : (∑ n ∈ D.lags, f n) =
    (∑ r, ∑ n ∈ D.lags, if n % (L : ℤ) = D.reps r then f n else 0) +
      ∑ n ∈ D.lags, if n % (L : ℤ) = 0 then f n else 0 := by
  classical
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rcases D.classes n hn with hz | ⟨r₀, hr⟩
  · have hh (r : Fin D.d) : n % (L : ℤ) ≠ D.reps r := by
      rw [hz]
      exact (D.reps_pos r).ne
    simp only [ite_eq_right (hh _), Finset.sum_const_zero, ite_eq_left hz, zero_add]
  · have hh (r : Fin D.d) : n % (L : ℤ) = D.reps r ↔ r = r₀ := by
      rw [hr]
      exact ⟨fun h => (D.reps_injective h).symm, fun h => by rw [h]⟩
    have hnzero : n % (L : ℤ) ≠ 0 := by rw [hr]; exact (D.reps_pos r₀).ne'
    simp_rw [hh]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_right hnzero, add_zero]

def slopeMoment (r : Fin D.d) : ℝ :=
  ∑ n ∈ D.lags, if n % (L : ℤ) = D.reps r then D.dual n * ((n / (L : ℤ) : ℤ) : ℝ) else 0

theorem quotient_eq_slope_fraction {n : ℤ} {r : Fin D.d} (hn : n % (L : ℤ) = D.reps r) :
    ((n / (L : ℤ) : ℤ) : ℝ) = ((n : ℝ) - (D.reps r : ℝ)) / L := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (by have h := D.period_ge; omega : L ≠ 0)
  apply (eq_div_iff hL).mpr
  have he := Int.emod_add_ediv_mul n (L : ℤ)
  rw [hn] at he
  have hr : (D.reps r : ℝ) + ((n / (L : ℤ) : ℤ) : ℝ) * L = n := by exact_mod_cast he
  linarith

end polyak.ModeLocking.RegularData
