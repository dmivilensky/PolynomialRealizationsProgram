import «2606.16671v2».Jacobi.Kernel
import «2606.16671v2».Spectral.OperatorNorm
import «2606.16671v2».Spectral.LinearResponseBound

/-!
Article: 2606.16671v2, Corollary 4.4.
First-order operator bound from any valid bounds on the two adjacent blocks.
Use: `«2606.16671v2».JacobiData.opNorm_linearResponse_blocks_le` feeds
`«2606.16671v2».JacobiData.opNorm_linearResponse_endpoint_le` (The linear operator bound of Theorem
4.3(iii), for any endpoint-maximizing chain).
Proof chain: `«2606.16671v2».Prefix.opNorm_linearResponse_le` — 2606.16671v2, Corollary 4.4;
Attained finite-drift bounds for the prefix recurrence.
-/
namespace «2606.16671v2».JacobiData
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Matrix BigOperators Matrix.Norms.L2Operator
variable (J : JacobiData) (I : SpectralInterval)
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The operator form of the k=1 block factorization in Theorem 4.3(i).

Exact identity `(J.realization I).linearResponse N H E = -(2 / (I.delta * J.den I N)) • ∑ s ∈
Finset.range N, aeval H (J.spectralBlock I (s + 1) (N - (s + 1))) * E s * aeval H
(J.spectralBlock I 0 s)`.

Use: `«2606.16671v2».JacobiData.opNorm_linearResponse_blocks_le` rewrites with this identity to
establish the stated quantitative bound `opNorm ((J.realization I).linearResponse N H E) ≤ (2 /
(I.delta * J.den I N)) * ∑ s ∈ Finset.range N, A s * opNorm (E s) * B s`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem linearResponse_blocks {N : ℕ} (h : J.Admissible I N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (E : ℕ → Matrix d d ℝ) :
    (J.realization I).linearResponse N H E = -(2 / (I.delta * J.den I N)) •
      ∑ s ∈ Finset.range N,
        aeval H (J.spectralBlock I (s + 1) (N - (s + 1))) * E s *
          aeval H (J.spectralBlock I 0 s) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let B := SpectralBasis.ofHermitian H hH
  apply B.coordinates_injective
  have hl := (J.realization I).linearResponse_coordinates B.Q H
    B.transpose_mul B.mul_transpose N E
  rw [B.diagonalize] at hl
  change (J.realization I).linearResponse N (Matrix.diagonal B.eigenvalues)
    (fun s => B.coordinates (E s)) = B.coordinates ((J.realization I).linearResponse N H E) at hl
  rw [← hl]
  have hsm (c : ℝ) (M : Matrix d d ℝ) : B.coordinates (c • M) = c • B.coordinates M := by
    simp [SpectralBasis.coordinates]
  have hsum (F : ℕ → Matrix d d ℝ) :
      B.coordinates (∑ s ∈ Finset.range N, F s) = ∑ s ∈ Finset.range N, B.coordinates (F s) := by
    simp [SpectralBasis.coordinates, Matrix.mul_sum, Matrix.sum_mul]
  rw [hsm, hsum]
  simp_rw [B.coordinates_mul]
  have hae (p : ℝ[X]) : B.coordinates (aeval H p) =
      Matrix.diagonal (fun i => p.eval (B.eigenvalues i)) := aeval_coordinates p H hH
  simp_rw [hae]
  ext i j
  simp only [Realization.diagonal_linearResponse_entry, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Finset.mul_sum, Matrix.diagonal_mul, Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro s hs
  rw [J.kernel_eq I h s (Finset.mem_range.mp hs)]
  simp only [spectralBlock_eval, leading]
  ring

/--
First-order operator bound from any valid bounds on the two adjacent blocks.

The stated quantitative bound `opNorm ((J.realization I).linearResponse N H E) ≤ (2 / (I.delta
* J.den I N)) * ∑ s ∈ Finset.range N, A s * opNorm (E s) * B s`.

Use: `«2606.16671v2».JacobiData.opNorm_linearResponse_endpoint_le` uses this bound to establish
the stated quantitative bound `opNorm ((J.realization I).linearResponse N H E) ≤ 2 * (N : ℝ) ^
2 * I.epsilon N * delta / I.delta`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.linearResponse_blocks`,
`«2606.16671v2».opNorm_smul`, `«2606.16671v2».SpectralInterval.delta_pos` with the arguments
shown in the proof.
-/
theorem opNorm_linearResponse_blocks_le {N : ℕ} (h : J.Admissible I N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (A B : ℕ → ℝ)
    (hA : ∀ s < N, 0 ≤ A s) (hB : ∀ s < N, 0 ≤ B s)
    (hleft : ∀ s < N, ∀ x ∈ Set.Icc (-1) 1,
      |(J.block (s + 1) (N - (s + 1))).eval x| ≤ A s)
    (hright : ∀ s < N, ∀ x ∈ Set.Icc (-1) 1, |(J.leading s).eval x| ≤ B s) :
    opNorm ((J.realization I).linearResponse N H E) ≤
      (2 / (I.delta * J.den I N)) *
        ∑ s ∈ Finset.range N, A s * opNorm (E s) * B s := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.linearResponse_blocks`,
  -- `«2606.16671v2».opNorm_smul`, `«2606.16671v2».SpectralInterval.delta_pos` with the
  -- arguments shown in the proof.
  rw [J.linearResponse_blocks I h H hH E, opNorm_smul,
    abs_neg, abs_of_pos (div_pos (by norm_num) (mul_pos I.delta_pos (h N le_rfl)))]
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (by norm_num) (mul_pos I.delta_pos (h N le_rfl)).le)
  unfold opNorm
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  have hsN := Finset.mem_range.mp hs
  have ha := opNorm_aeval_le (J.spectralBlock I (s + 1) (N - (s + 1))) I H hH hspec
    (A s) (hA s hsN) (fun lam hl => by
      rw [spectralBlock_eval]; exact hleft s hsN _ (I.z_mem hl))
  have hb := opNorm_aeval_le (J.spectralBlock I 0 s) I H hH hspec (B s) (hB s hsN)
    (fun lam hl => by rw [spectralBlock_eval]; exact hright s hsN _ (I.z_mem hl))
  calc
    _ ≤ (‖aeval H (J.spectralBlock I (s + 1) (N - (s + 1)))‖ * ‖E s‖) *
        ‖aeval H (J.spectralBlock I 0 s)‖ := (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hb
      (norm_nonneg _) (mul_nonneg (hA s hsN) (norm_nonneg _))

end
end «2606.16671v2».JacobiData
