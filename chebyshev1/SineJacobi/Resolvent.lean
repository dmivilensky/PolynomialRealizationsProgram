import chebyshev1.SineJacobi.Gain
import chebyshev1.Jacobi.Resolvent

/-!
Article: chebyshev1, Theorem 5.2.
The exact matrix-resolvent formulation in the finite part of Theorem 5.2.
Result: `chebyshev1.SineJacobi.gain_exact_resolvent` supplies the stated article conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Polynomial
open scoped BigOperators Matrix

/--
Exact identity `(1-(data N).matrix 0 N)⁻¹ s s = greenWeight N s.val`.

Use: `chebyshev1.SineJacobi.gain_exact_resolvent` rewrites with this identity to establish
exact identity `((data N).realization I).gain I N = 2*I.epsilon N/I.delta * Real.sqrt (∑ s :
Fin N, ((1-(data N).matrix 0 N)⁻¹ s s)^2)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_exact_resolvent`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem resolvent_diagonal (N : ℕ) (s : Fin N) :
    (1-(data N).matrix 0 N)⁻¹ s s = greenWeight N s.val := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs := s.isLt
  have hN : 0 < N := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hr := (data (n+1)).resolvent_diagonal n s 1 (data_aSq_nonneg (n+1))
  have hone : Matrix.scalar (Fin (n+1)) (1:ℝ) = 1 := by simp [Matrix.scalar]
  rw [hone, tail_eq_leading_of_end (n+1) (s.val+1) (n-s.val) (by omega)] at hr
  rw [hr]
  have hp : ((data (n+1)).leading (n+1)).eval 1 = 2/(2:ℝ)^(n+1) := by
    simp [terminal (n+1) (by omega)]
  rw [hp]
  unfold greenWeight endpoint
  rw [show n+1-s.val-1 = n-s.val by omega]
  have he : (2:ℝ)^(n+1) = 2^s.val*2^(n-s.val)*2 := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [he]
  field_simp

/--
Exact identity `Matrix.trace (1-(data N).matrix 0 N)⁻¹ = (N:ℝ)^2`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 5.2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.resolvent_diagonal`,
`chebyshev1.SineJacobi.greenWeight_sum` with the arguments shown in the proof.
-/
theorem resolvent_trace (N : ℕ) (hN : 0 < N) :
    Matrix.trace (1-(data N).matrix 0 N)⁻¹ = (N:ℝ)^2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag, resolvent_diagonal]
  rw [Fin.sum_univ_eq_sum_range]
  exact greenWeight_sum ⟨1,2,by norm_num,by norm_num⟩ N hN

/--
The exact matrix-resolvent formulation in the finite part of Theorem 5.2.

Exact identity `((data N).realization I).gain I N = 2*I.epsilon N/I.delta * Real.sqrt (∑ s :
Fin N, ((1-(data N).matrix 0 N)⁻¹ s s)^2)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 5.2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.gain_exact`,
`chebyshev1.SineJacobi.resolvent_diagonal` with the arguments shown in the proof.
-/
theorem gain_exact_resolvent (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ((data N).realization I).gain I N = 2*I.epsilon N/I.delta *
      Real.sqrt (∑ s : Fin N, ((1-(data N).matrix 0 N)⁻¹ s s)^2) := by
  rw [gain_exact I N hN]
  simp only [resolvent_diagonal]
  exact congrArg (fun t => 2*I.epsilon N/I.delta*Real.sqrt t)
    (Fin.sum_univ_eq_sum_range (fun s : ℕ => (greenWeight N s)^2) N).symm

end
end chebyshev1.SineJacobi
