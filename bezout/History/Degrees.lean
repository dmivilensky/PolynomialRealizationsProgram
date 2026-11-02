import bezout.History.Resolvent
import Mathlib.Algebra.Polynomial.BigOperators

/-!
Article: bezout, Theorem 2.1 (causal degree bounds).
Use: maximal-degree terminals force graded queries and graded responses.
Proof: the physical inverse is lower triangular and each causal edge raises
polynomial degree by at most one.
-/

namespace bezout.History

open Polynomial
open scoped BigOperators Polynomial
noncomputable section
variable {N : ℕ}

/-- The causally filtered form of the polynomial inverse row equation.
Article: bezout, Appendix A. Use: support and degree induction. -/
theorem resolvent_causal_row (h : bezout.History N) (s j : Fin N) :
    h.resolvent s j = (if s = j then 1 else 0) -
      ∑ k : Fin N, if k < s then h.coefficient s k * h.resolvent k j else 0 := by
  exact lowerSolve_eq (fun s j => h.coefficient s j)
    (fun k => if k = j then 1 else 0) s

/-- An error cannot propagate backwards to an earlier oracle call.
Article: bezout, Theorem 2.1. Use: the exact response degree bound. -/
theorem resolvent_zero (h : bezout.History N) (s j : Fin N) (hsj : s < j) :
    h.resolvent s j = 0 := by
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    rw [h.resolvent_causal_row]
    have he : s ≠ j := ne_of_lt hsj
    simp only [ite_eq_right he, zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k < s
    · simp [hk, ih k hk (lt_trans hk hsj)]
    · simp [hk]

/-- The inverse entry from call j to call s has degree at most s-j.
Article: bezout, Theorem 2.1. Use: terminal physical response degrees. -/
theorem resolvent_natDegree_le (h : bezout.History N) (s j : Fin N) :
    (h.resolvent s j).natDegree ≤ s.val - j.val := by
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    rw [h.resolvent_causal_row]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · split_ifs <;> simp
    · apply natDegree_sum_le_of_forall_le
      intro k _
      by_cases hk : k < s
      · simp only [ite_eq_left hk]
        by_cases hkj : k < j
        · simp [h.resolvent_zero k j hkj]
        · have hc : (h.coefficient s k).natDegree ≤ 1 := by
            exact (natDegree_mul_le (p := X) (q := C (h.a s k))).trans (by simp)
          have hb := (natDegree_mul_le (p := h.coefficient s k)
            (q := h.resolvent k j)).trans (add_le_add hc (ih k hk))
          exact hb.trans (by omega)
      · simp [hk]

/-- Query s has degree at most s for every causal coefficient history.
Article: bezout, Theorem 2.1. Use: exact degrees from terminal exactness. -/
theorem query_natDegree_le (h : bezout.History N) (s : Fin N) :
    (h.query s).natDegree ≤ s.val := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (h.resolvent_natDegree_le s j).trans (Nat.sub_le _ _)

/-- The physical response at call j has degree at most N-1-j.
Article: bezout, Theorem 2.1. Use: exact graded response factors. -/
theorem response_natDegree_le (h : bezout.History N) (j : Fin N) :
    (h.response j).natDegree ≤ N - 1 - j.val := by
  rw [response, natDegree_neg]
  apply natDegree_sum_le_of_forall_le
  intro s _
  exact (natDegree_C_mul_le _ _).trans
    ((h.resolvent_natDegree_le s j).trans (by omega))

/-- A history with N oracle calls has terminal degree at most N.
Article: bezout, Theorem 2.1. Use: the prescribed degree-N comparison class. -/
theorem terminal_natDegree_le (h : bezout.History N) :
    h.terminal.natDegree ≤ N := by
  rw [terminal]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · by_cases hN : N = 0
    · subst N
      simp
    · have hs : (∑ s, C (h.b s) * h.query s).natDegree ≤ N - 1 := by
        apply natDegree_sum_le_of_forall_le
        intro s _
        exact (natDegree_C_mul_le _ _).trans ((h.query_natDegree_le s).trans (by omega))
      have hm : (X * ∑ s, C (h.b s) * h.query s).natDegree ≤ 1 + (N - 1) :=
        natDegree_mul_le.trans (add_le_add (by simp) hs)
      exact hm.trans (by omega)

end
end bezout.History
