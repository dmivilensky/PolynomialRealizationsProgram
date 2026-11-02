import bezout.Synthesis.Coefficients
import bezout.History.Resolvent

/-!
Article: bezout, Theorem 2.1, synthesis and uniqueness of the causal history.
Use: converts the unique graded-basis coordinates into the actual finite
history coefficients, with strict causality proved from their construction.
Proof: reindex each earlier-query sum by its finite prefix and apply the
uniqueness of the triangular solve.
-/

namespace bezout
noncomputable section
open Polynomial
open scoped BigOperators

namespace NormalizedFamily
variable {N : ℕ} (Q : NormalizedFamily N)

/-- Fill the causally unavailable entries of each synthesized row with zero.
Use: supplies the actual strictly lower-triangular coefficient matrix. -/
def coefficient (s j : Fin N) : ℝ :=
  if hj : j < s then Q.row s ⟨j.val, hj⟩ else 0

/-- The synthesized coefficients are strictly lower triangular.
Use: witnesses that the reconstructed method belongs to the paper's history class. -/
theorem coefficient_triangular (s j : Fin N) (hsj : s ≤ j) : Q.coefficient s j = 0 := by
  simp [coefficient, not_lt.mpr hsj]

/-- Prefix reindexing of an arbitrary function on call indices.
Use: relates the graded-coordinate convention to the full finite history matrix. -/
theorem sum_before (s : Fin N) (f : Fin N → ℝ[X]) :
    (∑ j : Fin N, if j < s then f j else 0) =
      ∑ j : Fin s.val, f (j.castLE (Nat.le_of_lt s.isLt)) := by
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin N => j < s), f j := by
      rw [Finset.sum_filter]
    _ = _ := by
      symm
      apply Finset.sum_bij (fun j _ => j.castLE (Nat.le_of_lt s.isLt))
      · intro j _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact j.isLt
      · intro i _ j _ hij
        exact Fin.ext (congrArg (fun k : Fin N => k.val) hij)
      · intro j hj
        have hj' : j.val < s.val := (Finset.mem_filter.mp hj).2
        exact ⟨⟨j.val, hj'⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro j _
        rfl

/-- The full coefficient matrix gives exactly the synthesized row recurrence.
Use: this is the defining nominal-query equation of the reconstructed history. -/
theorem full_query_recurrence (s : Fin N) :
    Q.poly s = 1 -
      ∑ j : Fin N, if j < s then (X * C (Q.coefficient s j)) * Q.poly j else 0 := by
  rw [sum_before]
  rw [Q.query_recurrence s, Finset.mul_sum]
  apply congrArg (fun p : ℝ[X] => 1 - p)
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.castLE (Nat.le_of_lt s.isLt) < s := j.isLt
  have ha : Q.coefficient s (j.castLE (Nat.le_of_lt s.isLt)) = Q.row s j := by
    simp only [coefficient, dite_true, show j.castLE (Nat.le_of_lt s.isLt) < s from hj]
    exact congrArg (Q.row s) (Fin.ext rfl)
  rw [ha, mul_assoc]

/-- The unique actual history synthesized from the queries and terminal.
Use: the existence conclusion of the converse realization theorem. -/
def history (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ)) : History N where
  a := Q.coefficient
  b := Q.weights p hp
  triangular := Q.coefficient_triangular

/-- The actual synthesized history has exactly the prescribed nominal queries.
Use: the realization converse identifies polynomials of a genuine causal history. -/
theorem history_query (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ)) :
    (Q.history p hp).query = Q.poly := by
  rw [(Q.history p hp).query_eq_lowerSolve]
  apply Eq.symm
  apply History.lowerSolve_unique
  intro s
  exact Q.full_query_recurrence s

/-- The actual synthesized history has exactly the prescribed terminal polynomial.
Use: terminal exactness in the existence part of Theorem 2.1. -/
theorem history_terminal (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ))
    (hp0 : p.eval 0 = 1) : (Q.history p hp).terminal = p := by
  unfold History.terminal
  rw [Q.history_query]
  exact (Q.terminal_recurrence p hp hp0).symm

/-- The query family and terminal determine every coefficient of the history.
Use: the uniqueness part of the constructive realization theorem. -/
theorem history_unique (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ))
    (hp0 : p.eval 0 = 1) (h : History N)
    (hq : h.query = Q.poly) (ht : h.terminal = p) : h = Q.history p hp := by
  have hrow (s : Fin N) :
      (fun j : Fin s.val => h.a s (j.castLE (Nat.le_of_lt s.isLt))) = Q.row s := by
    apply Q.row_unique
    have hr := h.query_recurrence s
    rw [hq, sum_before] at hr
    exact hr
  have ha : h.a = Q.coefficient := by
    funext s j
    by_cases hj : j < s
    · have hr := congrFun (hrow s) ⟨j.val, hj⟩
      change h.a s j = Q.row s ⟨j.val, hj⟩ at hr
      simpa only [coefficient, hj, dite_true] using hr
    · rw [h.triangular s j (le_of_not_gt hj)]
      simp only [coefficient, hj, dite_false]
  have hb : h.b = Q.weights p hp := by
    apply Q.weights_unique p hp hp0
    rw [← ht]
    unfold History.terminal
    rw [hq]
  cases h
  congr

/-- A normalized graded family and normalized terminal determine one actual history.
Use: the complete converse existence-and-uniqueness assertion of Theorem 2.1. -/
theorem existsUnique_history (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ))
    (hp0 : p.eval 0 = 1) :
    ∃! h : History N, h.query = Q.poly ∧ h.terminal = p := by
  exact ⟨Q.history p hp, ⟨Q.history_query p hp, Q.history_terminal p hp hp0⟩,
    fun h hh => Q.history_unique p hp hp0 h hh.1 hh.2⟩

end NormalizedFamily
end
end bezout
