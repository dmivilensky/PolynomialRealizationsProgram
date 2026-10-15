import «2606.16671v2».Jacobi.PartitionPolynomial
import «2606.16671v2».Algebra.BlockWord

/-!
Article: 2606.16671v2, Theorem 4.3.
Equality in every finite order for chains whose blocks attain their maxima at one.
Use: `«2606.16671v2».JacobiData.G_eq_chebyshev_coeff_all` feeds `«2606.16671v2».SineJacobi.G_exact`
(All orders have exactly the Chebyshev partition constants).
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
variable (J : JacobiData) (I : SpectralInterval)

/--
The stated quantitative bound `J.endpointWeight n times ≤ J.partitionWeight n times`.

Use: `«2606.16671v2».JacobiData.partitionBound_ge_coeff` uses this bound to establish the
stated quantitative bound `(taylor 1 (J.leading N)).coeff k ≤ J.partitionBound N k`.

Article: 2606.16671v2, Theorem 4.3 via `«2606.16671v2».JacobiData.G_ge_chebyshev_coeff_all`.

Proof: Induct on `ts` while keeping `n` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem endpointWeight_le_partitionWeight (n : ℕ) (times : Finset ℕ) :
    J.endpointWeight n times ≤ J.partitionWeight n times := by
  -- Induct on `ts` while keeping `n` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  have hl (n : ℕ) (ts : List ℕ) :
      |blockWord (fun a k => (J.block a k).eval 1) (fun _ => 1) n ts| ≤
        blockWord J.blockBound (fun _ => 1) n ts := by
    induction ts generalizing n with
    | nil => exact J.block_eval_le_bound 0 n (by norm_num)
    | cons s ts ih =>
      simp only [blockWord, mul_one, abs_mul]
      exact mul_le_mul (J.block_eval_le_bound _ _ (by norm_num)) (ih s)
        (abs_nonneg _) (J.blockBound_nonneg _ _)
  exact (le_abs_self _).trans (hl n (times.sort (· ≥ ·)))

/--
Exact identity `J.endpointWeight n times = J.partitionWeight n times`.

Use: `«2606.16671v2».JacobiData.partitionBound_eq_coeff` uses this identity to establish exact
identity `J.partitionBound N k = (taylor 1 (J.leading N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `«2606.16671v2».blockWord_congr`,
`«2606.16671v2».wordValid_sort`, `«2606.16671v2».JacobiData.blockBound_endpoint` with the
arguments shown in the proof.
-/
theorem endpointWeight_eq_partitionWeight {N n : ℕ} (hm : J.EndpointMax N) (hn : n ≤ N)
    (times : Finset ℕ) (ht : times ⊆ Finset.range n) :
    J.endpointWeight n times = J.partitionWeight n times := by
  apply blockWord_congr _ _ _ hn (wordValid_sort n times ht)
  intro a k hak
  exact (J.blockBound_endpoint a k (hm a k hak)).symm

/--
The stated quantitative bound `(taylor 1 (J.leading N)).coeff k ≤ J.partitionBound N k`.

Use: `«2606.16671v2».JacobiData.G_ge_chebyshev_coeff` uses this bound to establish the stated
quantitative bound `2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k ≤ J.G N k`.

Article: 2606.16671v2, Theorem 4.3 via `«2606.16671v2».JacobiData.G_ge_chebyshev_coeff_all`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.taylor_leading_coeff`,
`«2606.16671v2».JacobiData.endpointWeight_le_partitionWeight` with the arguments shown in the
proof.
-/
theorem partitionBound_ge_coeff {N : ℕ} (h : J.Admissible I N) (k : ℕ) :
    (taylor 1 (J.leading N)).coeff k ≤ J.partitionBound N k := by
  rw [J.taylor_leading_coeff I h]
  exact Finset.sum_le_sum (fun times _ => J.endpointWeight_le_partitionWeight N times)

/--
Exact identity `J.partitionBound N k = (taylor 1 (J.leading N)).coeff k`.

Use: `«2606.16671v2».JacobiData.G_eq_chebyshev_coeff` rewrites with this identity to establish
exact identity `J.G N k = 2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem partitionBound_eq_coeff {N : ℕ} (h : J.Admissible I N) (hm : J.EndpointMax N) (k : ℕ) :
    J.partitionBound N k = (taylor 1 (J.leading N)).coeff k := by
  rw [J.taylor_leading_coeff I h]
  apply Finset.sum_congr rfl
  intro times ht
  exact (J.endpointWeight_eq_partitionWeight hm le_rfl times (Finset.mem_powersetCard.mp ht).1).symm

/--
The stated quantitative bound `2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k ≤ J.G N k`.

Use: `«2606.16671v2».JacobiData.G_ge_chebyshev_coeff_all` uses this bound to establish the
stated quantitative bound `2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k ≤ J.G N k`.

Article: 2606.16671v2, Theorem 4.3 via `«2606.16671v2».JacobiData.G_ge_chebyshev_coeff_all`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem G_ge_chebyshev_coeff {N k : ℕ} (h : J.Admissible I N)
    (hterminal : J.leading N = C (2 / (2 : ℝ)^N) * T ℝ N) (hk : k ≤ N) :
    2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k ≤ J.G N k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hc := J.partitionBound_ge_coeff I h k
  have he : (taylor 1 (J.leading N)).coeff k =
      (2 / (2 : ℝ)^N) * (taylor 1 (T ℝ N)).coeff k := by
    rw [hterminal, taylor_mul, taylor_C, coeff_C_mul]
  rw [he] at hc
  have hp : (2 : ℝ)^N = 2^k * 2^(N-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  have hc' := mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (N-k))
  unfold G
  convert hc' using 1
  rw [hp]
  field_simp

/--
Equality in every finite order for chains whose blocks attain their maxima at one.

Exact identity `J.G N k = 2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k`.

Use: `«2606.16671v2».JacobiData.G_eq_chebyshev_coeff_all` uses this identity to establish exact
identity `J.G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem G_eq_chebyshev_coeff {N k : ℕ} (h : J.Admissible I N) (hm : J.EndpointMax N)
    (hterminal : J.leading N = C (2 / (2 : ℝ)^N) * T ℝ N) (hk : k ≤ N) :
    J.G N k = 2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  unfold G
  rw [J.partitionBound_eq_coeff I h hm, hterminal, taylor_mul, taylor_C, coeff_C_mul]
  have hp : (2 : ℝ)^N = 2^k * 2^(N-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  rw [hp]
  field_simp


/--
Exact identity `J.G N k = 0`.

Use: `«2606.16671v2».JacobiData.G_eq_chebyshev_coeff_all` rewrites with this identity to
establish exact identity `J.G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem G_zero_above_horizon {N k : ℕ} (hk : N < k) : J.G N k = 0 := by
  have he : (Finset.range N).powersetCard k = ∅ := Finset.powersetCard_eq_empty.mpr (by simpa using hk)
  simp [G, partitionBound, he]

/--
The stated quantitative bound `2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k ≤ J.G N k`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem 4.3.

Proof: Separate `k ≤ N` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem G_ge_chebyshev_coeff_all {N : ℕ} (h : J.Admissible I N)
    (ht : J.leading N = C (2/(2:ℝ)^N)*T ℝ N) (k : ℕ) :
    2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k ≤ J.G N k := by
  by_cases hk : k ≤ N
  · exact J.G_ge_chebyshev_coeff I h ht hk
  · have hc : (taylor 1 (T ℝ N)).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simp; omega)
    rw [J.G_zero_above_horizon (by omega), hc, mul_zero]

/--
Exact identity `J.G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k`.

Use: `«2606.16671v2».SineJacobi.G_exact` uses this identity to establish the identity `(data
N).G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Separate `k ≤ N` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem G_eq_chebyshev_coeff_all {N : ℕ} (h : J.Admissible I N) (hm : J.EndpointMax N)
    (ht : J.leading N = C (2/(2:ℝ)^N)*T ℝ N) (k : ℕ) :
    J.G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k := by
  by_cases hk : k ≤ N
  · exact J.G_eq_chebyshev_coeff I h hm ht hk
  · have hc : (taylor 1 (T ℝ N)).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simp; omega)
    rw [J.G_zero_above_horizon (by omega), hc, mul_zero]

end
end «2606.16671v2».JacobiData
