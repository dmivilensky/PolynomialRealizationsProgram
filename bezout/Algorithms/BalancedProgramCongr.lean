import bezout.Algorithms.BalancedRegisters

/-!
Article: bezout, Algorithm 2, inactive scalar preparation entries.
Use: cached implementations may fill unused weights and impulses by zero;
only coefficients read by an active physical branch affect the program.
Proof: expand the in-place instruction lists and compare each active branch.
-/

namespace bezout.Algorithms.BalancedParameters
noncomputable section
variable {N : ℕ}

/-- Two Balanced scalar tables define exactly the same physical program whenever
they agree on the entries actually read by the four live prediction branches. -/
theorem program_eq_of_active (p q : BalancedParameters N)
    (hw : ∀ k, k.val+4<N → p.weights k = q.weights k)
    (hi : ∀ k d, 1≤d → d≤4 → k.val+d<N →
      p.impulse (k.val+d) k = q.impulse (k.val+d) k)
    (hr : p.readout=q.readout) : p.program=q.program := by
  unfold program
  congr 1
  funext k
  rw [hr]
  by_cases h4 : k.val+4<N
  · rw [ite_eq_left h4, hw k h4, hi k 4 (by omega) (by omega) h4]
    have h1 : k.val+1<N := by omega
    have h2 : k.val+2<N := by omega
    have h3 : k.val+3<N := by omega
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3,
      hi k 1 (by omega) (by omega) h1, hi k 2 (by omega) (by omega) h2,
      hi k 3 (by omega) (by omega) h3]
    simp [h4,h1,h2,h3]
  · rw [ite_eq_right h4]
    by_cases h1 : k.val+1<N
    · rw [ite_eq_left h1, hi k 1 (by omega) (by omega) h1]
      by_cases h2 : k.val+2<N
      · rw [ite_eq_left h2, hi k 2 (by omega) (by omega) h2]
        by_cases h3 : k.val+3<N
        · rw [ite_eq_left h3, hi k 3 (by omega) (by omega) h3]
          simp [h4,h1,h2,h3]
        · rw [ite_eq_right h3]
          simp [h4,h1,h2,h3]
      · have h3 : ¬k.val+3<N := by omega
        rw [ite_eq_right h2, ite_eq_right h3]
        simp [h4,h1,h2,h3]
    · have h2 : ¬k.val+2<N := by omega
      have h3 : ¬k.val+3<N := by omega
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
      simp [h4,h1,h2,h3]

end
end bezout.Algorithms.BalancedParameters
