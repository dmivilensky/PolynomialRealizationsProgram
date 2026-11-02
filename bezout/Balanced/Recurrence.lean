import bezout.Balanced.Basis

/-!
Article: bezout, Algorithm 2 and Equation `eq:impulses`.
Use: the fourth-order recurrence closes the four prediction slots of Balanced.
Proof: subtract the two Chebyshev three-term recurrences, then substitute the
exact stopped-parity differences; all divisors have proved positive weights.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- Consecutive parity differences satisfy the Chebyshev second-order recurrence. -/
theorem chebyshev_difference_four (s : ℕ) (x : ℝ) :
    (T ℝ (s + 4)).eval x - (T ℝ (s + 2)).eval x =
      2 * x * ((T ℝ (s + 3)).eval x - (T ℝ (s + 1)).eval x) -
        ((T ℝ (s + 2)).eval x - (T ℝ s).eval x) := by
  have h1 := congrArg (fun p : ℝ[X] => p.eval x) (T_add_two ℝ (s : ℤ))
  have h3 := congrArg (fun p : ℝ[X] => p.eval x) (T_add_two ℝ ((s : ℤ) + 2))
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at h1 h3
  ring_nf at h1 h3 ⊢
  linarith

/-- The full fourth-order scalar polynomial recurrence used by the six-slot algorithm. -/
theorem psi_eval_fourth_order {N s : ℕ} (hN : 2 ≤ N) (hs : s + 4 < N) (x : ℝ) :
    (psi N (s + 4)).eval x =
      (2 * x * omega N (s + 4) / omega N (s + 3)) * (psi N (s + 3)).eval x +
      (1 - omega N (s + 4) / omega N (s + 2)) * (psi N (s + 2)).eval x -
      (2 * x * omega N (s + 4) / omega N (s + 3)) * (psi N (s + 1)).eval x +
      (omega N (s + 4) / omega N (s + 2)) * (psi N s).eval x := by
  have h2 := congrArg (fun p : ℝ[X] => p.eval x) (psi_add_two N s)
  have h3 := congrArg (fun p : ℝ[X] => p.eval x) (psi_add_two N (s + 1))
  have h4 := congrArg (fun p : ℝ[X] => p.eval x) (psi_add_two N (s + 2))
  norm_num only [eval_add, eval_mul, eval_C, eval_sub, Nat.add_assoc,
    Nat.cast_add, Nat.cast_ofNat] at h2 h3 h4
  have hd := chebyshev_difference_four s x
  norm_num only [add_assoc] at h2 h3 h4
  have hw2 := ne_of_gt (omega_pos hN (show s + 2 < N by omega))
  have hw3 := ne_of_gt (omega_pos hN (show s + 3 < N by omega))
  field_simp
  linear_combination
    omega N (s + 2) * omega N (s + 3) * h4 -
    2 * x * omega N (s + 4) * omega N (s + 2) * h3 +
    omega N (s + 4) * omega N (s + 3) * h2 +
    omega N (s + 4) * omega N (s + 2) * omega N (s + 3) * hd

/-- The scalar preparation normalizers obey precisely the prediction recurrence. -/
theorem normalizer_fourth_order (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 4 < N) :
    normalizer I N (s + 4) =
      (2 * I.eta * omega N (s + 4) / omega N (s + 3)) * normalizer I N (s + 3) +
      (1 - omega N (s + 4) / omega N (s + 2)) * normalizer I N (s + 2) -
      (2 * I.eta * omega N (s + 4) / omega N (s + 3)) * normalizer I N (s + 1) +
      (omega N (s + 4) / omega N (s + 2)) * normalizer I N s :=
  psi_eval_fourth_order hN hs I.eta

end
end bezout.Balanced
