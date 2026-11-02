import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine positive-pivot barrier principle.
Use: rule out persistent lower-barrier violations for the true positive shifted Jacobi pivots before proving actual Nevai asymptotic stability.
Source: elementary actual scalar descent and the real Archimedean property.
-/

namespace krylov.LinearAlgebra
noncomputable section

/-- A genuinely positive infinite scalar sequence cannot have a fixed positive descent whenever it falls below an actual barrier.
Use: A genuinely positive infinite scalar sequence cannot have a fixed positive descent whenever it falls below an actual barrier.
Article: main_krylov, prop:phi(c), genuine positive-pivot barrier principle.
Proof: A true barrier violation propagates to an actual arithmetic descent; enough real iterations contradict genuine positivity. -/
theorem positive_sequence_no_descent (s : ℕ → ℝ) (hs : ∀ n,0 < s n)
    (c eta : ℝ) (heta : 0 < eta) (N : ℕ)
    (hstep : ∀ n,N≤n → s n<c → s (n+1)≤s n-eta) :
    ∀ n,N≤n → c≤s n := by
  -- A true barrier violation forces every later actual value to decrease by the same positive amount.
  intro n hn
  by_contra hc
  have hnc : s n<c := lt_of_not_ge hc
  have hbound (k : ℕ) : s (n+k)≤s n-k*eta := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hsc : s (n+k)<c := lt_of_le_of_lt (ih.trans (sub_le_self _ (mul_nonneg (Nat.cast_nonneg k) heta.le))) hnc
      have hnext := hstep (n+k) (by omega) hsc
      have he : n+(k+1)=n+k+1 := by omega
      rw [he]
      push_cast
      linarith
  -- The actual Archimedean index makes the genuine positive sequence cross zero, giving the contradiction.
  obtain ⟨k,hk⟩ := exists_nat_gt (s n/eta)
  have ht : s n<(k:ℝ)*eta := (div_lt_iff₀ heta).mp hk
  have hpos := hs (n+k)
  have hb := hbound k
  linarith
end
end krylov.LinearAlgebra
