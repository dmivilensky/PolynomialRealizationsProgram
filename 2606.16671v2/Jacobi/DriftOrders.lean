import «2606.16671v2».Jacobi.BlockBounds
import «2606.16671v2».Realization.Multilinear

/-!
Article: 2606.16671v2, Theorem 4.3.
The normalized bound in Theorem 4.3(ii), including orders above the horizon.
Use: `«2606.16671v2».JacobiData.opNorm_driftOrder_G_le` feeds
`«2606.16671v2».JacobiData.opNorm_driftOrder_endpoint_le` (op Norm drift Order endpoint le).
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) (I : SpectralInterval)
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The actual output contribution containing exactly `k` Hessian insertions.

Use: `«2606.16671v2».JacobiData.driftOrder_eq_zero` uses this definition to establish exact
identity `J.driftOrder I N k H E = 0`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.
-/
def driftOrder (N k : ℕ) (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) : Matrix d d ℝ :=
  (J.realization I).contract (degreeTerm (fun s => (J.realization I).operatorStep s H)
    (fun s => (J.realization I).operatorInsertion s (E s)) N k)

/--
Exact identity `J.driftOrder I N k H E = ((-(2 / I.delta)) ^ k / J.den I N) • ∑ times ∈
(Finset.range N).powersetCard k, J.operatorWord I H E N times`.

Use: `«2606.16671v2».JacobiData.opNorm_driftOrder_le` rewrites with this identity to establish
the stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ (2 / I.delta) ^ k / J.den I N
* delta ^ k * J.partitionBound N k`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem driftOrder_words {N : ℕ} (h : J.Admissible I N) (k : ℕ)
    (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) :
    J.driftOrder I N k H E = ((-(2 / I.delta)) ^ k / J.den I N) •
      ∑ times ∈ (Finset.range N).powersetCard k, J.operatorWord I H E N times := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  unfold driftOrder degreeTerm
  change (J.realization I).contractLinear _ = _
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro times ht
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
  simpa only [Realization.contractLinear_apply, hcard] using
    J.insertionTerm_blocks I h N le_rfl H E times hsub

/--
Exact identity `J.driftOrder I N 0 H E = (J.realization I).operatorTransfer N (fun _ => H)`.

Use: `«2606.16671v2».JacobiData.opNorm_finiteDrift_endpoint_le` rewrites with this identity to
establish the stated quantitative bound `opNorm ((J.realization I).operatorTransfer N (fun s =>
H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem driftOrder_zero (N : ℕ) (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) :
    J.driftOrder I N 0 H E = (J.realization I).operatorTransfer N (fun _ => H) := by simp [driftOrder, Realization.operatorTransfer]

/--
Exact identity `J.driftOrder I N 1 H E = (J.realization I).linearResponse N H E`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: 2606.16671v2, Theorem 4.3.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem driftOrder_one (N : ℕ) (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) :
    J.driftOrder I N 1 H E = (J.realization I).linearResponse N H E := rfl

/--
Exact identity `J.driftOrder I N k H E = 0`.

Use: `«2606.16671v2».JacobiData.opNorm_driftOrder_G_le` rewrites with this identity to
establish the stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ I.epsilon N / 2 * (4
* delta / I.delta)^k * J.G N k`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Use the identities/estimates `«2606.16671v2».degreeTerm_eq_zero_of_lt` with the
arguments shown in the proof.
-/
theorem driftOrder_eq_zero {N k : ℕ} (hk : N < k)
    (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) : J.driftOrder I N k H E = 0 := by
  unfold driftOrder
  rw [degreeTerm_eq_zero_of_lt _ _ hk]
  exact (J.realization I).contractLinear.map_zero

/--
Exact identity `(J.realization I).operatorTransfer N (fun s => H + E s) = ∑ k ∈ Finset.range (N
+ 1), J.driftOrder I N k H E`.

Use: `«2606.16671v2».JacobiData.opNorm_finiteDrift_endpoint_le` rewrites with this identity to
establish the stated quantitative bound `opNorm ((J.realization I).operatorTransfer N (fun s =>
H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Use the identities/estimates
`«2606.16671v2».Realization.operatorTransfer_affine_by_degree` with the arguments shown in the
proof.
-/
theorem operatorTransfer_driftOrders (N : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) :
    (J.realization I).operatorTransfer N (fun s => H + E s) =
      ∑ k ∈ Finset.range (N + 1), J.driftOrder I N k H E := by simpa [driftOrder] using (J.realization I).operatorTransfer_affine_by_degree N H E 1

/--
The stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ (2 / I.delta) ^ k / J.den I N
* delta ^ k * J.partitionBound N k`.

Use: `«2606.16671v2».JacobiData.opNorm_driftOrder_G_le` uses this bound to establish the stated
quantitative bound `opNorm (J.driftOrder I N k H E) ≤ I.epsilon N / 2 * (4 * delta / I.delta)^k
* J.G N k`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Use the identities/estimates `«2606.16671v2».SpectralInterval.delta_pos`,
`«2606.16671v2».JacobiData.driftOrder_words`, `«2606.16671v2».opNorm_smul` with the arguments
shown in the proof.
-/
theorem opNorm_driftOrder_le {N : ℕ} (h : J.Admissible I N) (k : ℕ)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (J.driftOrder I N k H E) ≤
      (2 / I.delta) ^ k / J.den I N * delta ^ k * J.partitionBound N k := by
  -- Use the identities/estimates `«2606.16671v2».SpectralInterval.delta_pos`,
  -- `«2606.16671v2».JacobiData.driftOrder_words`, `«2606.16671v2».opNorm_smul` with the
  -- arguments shown in the proof.
  have hc : 0 ≤ (2 / I.delta) ^ k / J.den I N :=
    div_nonneg (pow_nonneg (div_nonneg (by norm_num) I.delta_pos.le) _) (h N le_rfl).le
  rw [J.driftOrder_words I h, opNorm_smul, abs_div, abs_pow, abs_neg,
    abs_of_pos (div_pos (by norm_num) I.delta_pos), abs_of_pos (h N le_rfl)]
  calc
    _ ≤ ((2 / I.delta) ^ k / J.den I N) *
        ∑ times ∈ (Finset.range N).powersetCard k, opNorm (J.operatorWord I H E N times) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc
    _ ≤ ((2 / I.delta) ^ k / J.den I N) *
        ∑ times ∈ (Finset.range N).powersetCard k, delta ^ k * J.partitionWeight N times := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro times ht
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
      simpa only [hcard] using J.opNorm_operatorWord_le I N H hH hspec E delta hd hE N le_rfl times hsub
    _ = _ := by rw [← Finset.mul_sum]; exact (mul_assoc _ _ _).symm

/--
The normalized bound in Theorem 4.3(ii), including orders above the horizon.

The stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ I.epsilon N / 2 * (4 * delta /
I.delta)^k * J.G N k`.

Use: `«2606.16671v2».JacobiData.opNorm_driftOrder_endpoint_le` uses this bound to establish the
stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ I.epsilon N * (2*delta/I.delta)^k
* (taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Separate `k ≤ N` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem opNorm_driftOrder_G_le {N : ℕ} (h : J.Admissible I N)
    (hterminal : J.leading N = C (2 / (2 : ℝ)^N) * T ℝ N) (k : ℕ)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (J.driftOrder I N k H E) ≤
      I.epsilon N / 2 * (4 * delta / I.delta)^k * J.G N k := by
  -- Separate `k ≤ N` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hk : k ≤ N
  · have hden : J.den I N = (2 / (2 : ℝ)^N) * I.den N := by
      simp [den, hterminal, SpectralInterval.den]
    have hp : (2 : ℝ)^N = 2^k * 2^(N-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
    convert J.opNorm_driftOrder_le I h k H hH hspec E delta hd hE using 1
    dsimp [G, SpectralInterval.epsilon]
    rw [hden, hp]
    simp only [div_pow, mul_pow]
    have hfour : (4 : ℝ)^k = 2^k * 2^k := by rw [← mul_pow]; norm_num
    rw [hfour]
    field_simp
  · have hempty : (Finset.range N).powersetCard k = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using Nat.lt_of_not_ge hk)
    simp [J.driftOrder_eq_zero I (Nat.lt_of_not_ge hk) H E, G, partitionBound, hempty, opNorm]

end
end «2606.16671v2».JacobiData
