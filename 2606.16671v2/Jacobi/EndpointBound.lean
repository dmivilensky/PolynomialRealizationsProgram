import «2606.16671v2».Jacobi.LinearResponse
import «2606.16671v2».Realization.StaticShift

/-!
Article: 2606.16671v2, Corollary 4.4.
The linear operator bound of Theorem 4.3(iii), for any endpoint-maximizing chain.
Use: `«2606.16671v2».JacobiData.opNorm_linearResponse_endpoint_le` feeds
`«2606.16671v2».SineJacobi.opNorm_linearResponse_le` (op Norm linear Response le).
Proof chain: `«2606.16671v2».Prefix.opNorm_linearResponse_le` — 2606.16671v2, Corollary 4.4;
Attained finite-drift bounds for the prefix recurrence.
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial
open scoped BigOperators
variable (J : JacobiData) (I : SpectralInterval)

/--
All contiguous blocks used by the horizon attain their absolute maximum at one.

Use: `«2606.16671v2».JacobiData.opNorm_linearResponse_endpoint_le` uses this definition to
establish the stated quantitative bound `opNorm ((J.realization I).linearResponse N H E) ≤ 2 *
(N : ℝ) ^ 2 * I.epsilon N * delta / I.delta`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.
-/
def EndpointMax (N : ℕ) : Prop :=
  ∀ a n, a + n ≤ N → ∀ x ∈ Set.Icc (-1) 1, |(J.block a n).eval x| ≤ (J.block a n).eval 1

/--
The linear operator bound of Theorem 4.3(iii), for any endpoint-maximizing chain.

The stated quantitative bound `opNorm ((J.realization I).linearResponse N H E) ≤ 2 * (N : ℝ) ^
2 * I.epsilon N * delta / I.delta`.

Use: `«2606.16671v2».Prefix.opNorm_linearResponse_le` uses this bound to establish the stated
quantitative bound `opNorm ((realization I).linearResponse N H E) ≤ 2 * (N : ℝ) ^ 2 * I.epsilon
N * delta / I.delta`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem opNorm_linearResponse_endpoint_le {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (h : J.Admissible I N) (hmax : J.EndpointMax N)
    (hfinal : (J.realization I).residualPolynomial N = I.residual N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((J.realization I).linearResponse N H E) ≤
      2 * (N : ℝ) ^ 2 * I.epsilon N * delta / I.delta := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let A (s : ℕ) := (J.block (s + 1) (N - (s + 1))).eval 1
  let B (s : ℕ) := (J.leading s).eval 1
  have ha (s : ℕ) (hs : s < N) : 0 ≤ A s :=
    (abs_nonneg _).trans (hmax (s + 1) (N - (s + 1)) (by omega) 1 (by norm_num))
  have hb (s : ℕ) (hs : s < N) : 0 ≤ B s :=
    (abs_nonneg _).trans (hmax 0 s (by omega) 1 (by norm_num))
  have bound := J.opNorm_linearResponse_blocks_le I h H hH hspec E A B ha hb
    (fun s hs => hmax (s + 1) (N - (s + 1)) (by omega))
    (fun s hs => hmax 0 s (by omega))
  have hsum : ∑ s ∈ Finset.range N, (J.realization I).kernel N s I.mu I.mu =
      -(2 / (I.delta * J.den I N)) * ∑ s ∈ Finset.range N, A s * B s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [J.kernel_eq I h s (Finset.mem_range.mp hs), I.z_mu]
    dsimp [A, B]
    ring
  have hd := (J.realization I).kernel_sum_derivative N I.mu
  rw [hfinal, I.residual_derivative_eval_mu] at hd
  have hc : (2 / (I.delta * J.den I N)) * ∑ s ∈ Finset.range N, A s * B s =
      2 * (N : ℝ) ^ 2 * I.epsilon N / I.delta := by
    calc _ = -(∑ s ∈ Finset.range N, (J.realization I).kernel N s I.mu I.mu) := by rw [hsum]; ring
      _ = _ := by rw [hd]; ring
  calc
    _ ≤ _ := bound
    _ ≤ (2 / (I.delta * J.den I N)) * ∑ s ∈ Finset.range N, A s * delta * B s := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (mul_pos I.delta_pos (h N le_rfl)).le)
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hE s (Finset.mem_range.mp hs)) (ha s (Finset.mem_range.mp hs)))
        (hb s (Finset.mem_range.mp hs))
    _ = delta * ((2 / (I.delta * J.den I N)) * ∑ s ∈ Finset.range N, A s * B s) := by
      simp_rw [show ∀ s, A s * delta * B s = delta * (A s * B s) by intro s; ring]
      rw [← Finset.mul_sum]
      ring
    _ = _ := by rw [hc]; ring

end
end «2606.16671v2».JacobiData
