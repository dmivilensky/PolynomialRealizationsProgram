import chebyshev1.Jacobi.PrefixBounds
import chebyshev1.Jacobi.FiniteBounds

/-!
Article: chebyshev1, Corollary 4.4.
Prefix Finite Bounds.
Result: `chebyshev1.Prefix.opNorm_driftRemainder_cosh_le` supplies the stated article
conclusion.
-/
namespace chebyshev1.Prefix
noncomputable section
open Polynomial Polynomial.Chebyshev
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
Exact identity `jacobiData.leading N = C (2/(2:ℝ)^N) * T ℝ N`.

Use: `chebyshev1.Prefix.opNorm_driftRemainder_cosh_le` uses this identity to establish the
stated quantitative bound `opNorm ((realization I).driftRemainder N H E) ≤ (2/3:ℝ)*I.epsilon
N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem jacobi_terminal {N : ℕ} (hN : 0 < N) :
    jacobiData.leading N = C (2/(2:ℝ)^N) * T ℝ N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [jacobi_leading]
  congr 2
  rw [div_pow, pow_succ]
  field_simp
  simp

/--
The stated quantitative bound `opNorm ((realization I).operatorTransfer N (fun s => H+E s) -
aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Use: `chebyshev1.Nonlinear.MethodFamily.finiteDrift_le` uses this identity to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N (fun s =>
H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: chebyshev1, Corollary 4.4.

Proof: Use the identities/estimates `chebyshev1.JacobiData.opNorm_finiteDrift_endpoint_le`,
`chebyshev1.Prefix.jacobi_admissible`, `chebyshev1.Prefix.jacobi_endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_finiteDrift_le (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((realization I).operatorTransfer N (fun s => H+E s) - aeval H (I.residual N)) ≤
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1) := by
  -- Use the identities/estimates `chebyshev1.JacobiData.opNorm_finiteDrift_endpoint_le`,
  -- `chebyshev1.Prefix.jacobi_admissible`, `chebyshev1.Prefix.jacobi_endpointMax` with
  -- the arguments shown in the proof.
  have hb := jacobiData.opNorm_finiteDrift_endpoint_le I (jacobi_admissible I N)
    (jacobi_endpointMax N) (jacobi_terminal hN) H hH hspec E delta hd hE
  rwa [jacobi_realization] at hb

/--
The stated quantitative bound `opNorm ((realization I).driftRemainder N H E) ≤ I.epsilon N *
((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 4.4.

Proof: Use the identities/estimates
`chebyshev1.JacobiData.opNorm_driftRemainder_endpoint_le`,
`chebyshev1.Prefix.jacobi_admissible`, `chebyshev1.Prefix.jacobi_endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_driftRemainder_le (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((realization I).driftRemainder N H E) ≤
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta) := by
  -- Use the identities/estimates
  -- `chebyshev1.JacobiData.opNorm_driftRemainder_endpoint_le`,
  -- `chebyshev1.Prefix.jacobi_admissible`, `chebyshev1.Prefix.jacobi_endpointMax` with
  -- the arguments shown in the proof.
  have hb := jacobiData.opNorm_driftRemainder_endpoint_le I hN (jacobi_admissible I N)
    (jacobi_endpointMax N) (jacobi_terminal hN) H hH hspec E delta hd hE
  rwa [jacobi_realization] at hb

/--
The stated quantitative bound `opNorm ((realization I).driftRemainder N H E) ≤
(2/3:ℝ)*I.epsilon N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 4.4.

Proof: Use the identities/estimates `chebyshev1.JacobiData.opNorm_driftRemainder_cosh_le`,
`chebyshev1.Prefix.jacobi_admissible`, `chebyshev1.Prefix.jacobi_endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_driftRemainder_cosh_le (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((realization I).driftRemainder N H E) ≤
      (2/3:ℝ)*I.epsilon N*(N:ℝ)^4*(delta/I.delta)^2 *
        Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta)) := by
  -- Use the identities/estimates `chebyshev1.JacobiData.opNorm_driftRemainder_cosh_le`,
  -- `chebyshev1.Prefix.jacobi_admissible`, `chebyshev1.Prefix.jacobi_endpointMax` with
  -- the arguments shown in the proof.
  have hb := jacobiData.opNorm_driftRemainder_cosh_le I hN (jacobi_admissible I N)
    (jacobi_endpointMax N) (jacobi_terminal hN) H hH hspec E delta hd hE
  rwa [jacobi_realization] at hb

end
end chebyshev1.Prefix
