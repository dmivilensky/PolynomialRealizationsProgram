import «2606.16671v2».Jacobi.DriftOrders
import «2606.16671v2».Algebra.BlockWord

/-!
Article: 2606.16671v2, Theorem 4.3.
A product of the paper's normalized block maxima equals the defining weight of G_k.
Result: `«2606.16671v2».JacobiData.G_eq_normalized_partitionBound` supplies the stated article
conclusion.
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) (I : SpectralInterval)
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The paper's normalized principal-block determinant, including the empty block.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 4.3.
-/
def normalizedBlock (a n : ℕ) : ℝ[X] := C ((2:ℝ)^n) * J.block a n

/--
Defines `normalizedOperatorWord` of type `Matrix d d ℝ` by `blockWord (fun a k => (2:ℝ)^k •
aeval H (J.spectralBlock I a k)) E N (times.sort (· ≥ ·))`.

Use: `«2606.16671v2».JacobiData.normalizedOperatorWord_eq` uses this definition to establish
exact identity `J.normalizedOperatorWord I H E N times = (2:ℝ)^(N-times.card) • J.operatorWord
I H E N times`.

Article: 2606.16671v2, Theorem 4.3 via `«2606.16671v2».JacobiData.driftOrder_normalized`.
-/
def normalizedOperatorWord (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ)
    (N : ℕ) (times : Finset ℕ) : Matrix d d ℝ :=
  blockWord (fun a k => (2:ℝ)^k • aeval H (J.spectralBlock I a k)) E N (times.sort (· ≥ ·))

/--
Exact identity `J.normalizedOperatorWord I H E N times = (2:ℝ)^(N-times.card) • J.operatorWord
I H E N times`.

Use: `«2606.16671v2».JacobiData.driftOrder_normalized` rewrites with this identity to establish
exact identity `J.driftOrder I N k H E = (I.epsilon N/2 * (-(4/I.delta))^k) • ∑ times ∈
(Finset.range N).powersetCard k, J.normalizedOperatorWord I H E N times`.

Article: 2606.16671v2, Theorem 4.3 via `«2606.16671v2».JacobiData.driftOrder_normalized`.

Proof: Use the identities/estimates `«2606.16671v2».blockWord_scale`,
`«2606.16671v2».wordValid_sort` with the arguments shown in the proof.
-/
theorem normalizedOperatorWord_eq (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ)
    (N : ℕ) (times : Finset ℕ) (ht : times ⊆ Finset.range N) :
    J.normalizedOperatorWord I H E N times =
      (2:ℝ)^(N-times.card) • J.operatorWord I H E N times := by
  unfold normalizedOperatorWord operatorWord
  simpa only [Finset.length_sort] using
    blockWord_scale (fun a k => aeval H (J.spectralBlock I a k)) E 2 (wordValid_sort N times ht)

/--
The exact normalization and signs in Theorem 4.3(i).

Exact identity `J.driftOrder I N k H E = (I.epsilon N/2 * (-(4/I.delta))^k) • ∑ times ∈
(Finset.range N).powersetCard k, J.normalizedOperatorWord I H E N times`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem 4.3.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem driftOrder_normalized {N k : ℕ} (h : J.Admissible I N)
    (hterminal : J.leading N = C (2/(2:ℝ)^N) * T ℝ N) (hk : k ≤ N)
    (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) :
    J.driftOrder I N k H E = (I.epsilon N/2 * (-(4/I.delta))^k) •
      ∑ times ∈ (Finset.range N).powersetCard k, J.normalizedOperatorWord I H E N times := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [J.driftOrder_words I h, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro times ht
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
  rw [J.normalizedOperatorWord_eq I H E N times hsub, hcard, smul_smul]
  congr 1
  have hden : J.den I N = (2/(2:ℝ)^N)*I.den N := by
    simp [den, hterminal, SpectralInterval.den]
  have hp : (2:ℝ)^N = 2^k * 2^(N-k) := by rw [← pow_add, Nat.add_sub_of_le hk]
  rw [hden, hp]
  dsimp [SpectralInterval.epsilon]
  rw [show -(4/I.delta) = -(2/I.delta)*2 by ring, mul_pow]
  field_simp

/--
A product of the paper's normalized block maxima equals the defining weight of G_k.

Exact identity `blockWord (fun a k => (2:ℝ)^k * J.blockBound a k) (fun _ => 1) N (times.sort (·
≥ ·)) = (2:ℝ)^(N-times.card) * J.partitionWeight N times`.

Use: `«2606.16671v2».JacobiData.G_eq_normalized_partitionBound` rewrites with this identity to
establish exact identity `J.G N k = ∑ times ∈ (Finset.range N).powersetCard k, blockWord (fun a
n => (2:ℝ)^n * J.blockBound a n) (fun _ => 1) N (times.sort (· ≥ ·))`.

Article: 2606.16671v2, Theorem 4.3 via
`«2606.16671v2».JacobiData.G_eq_normalized_partitionBound`.

Proof: Use the identities/estimates `«2606.16671v2».blockWord_scale`,
`«2606.16671v2».wordValid_sort` with the arguments shown in the proof.
-/
theorem normalized_partitionWeight (N : ℕ) (times : Finset ℕ) (ht : times ⊆ Finset.range N) :
    blockWord (fun a k => (2:ℝ)^k * J.blockBound a k) (fun _ => 1) N (times.sort (· ≥ ·)) =
      (2:ℝ)^(N-times.card) * J.partitionWeight N times := by
  simpa only [smul_eq_mul, Finset.length_sort, partitionWeight] using
    blockWord_scale J.blockBound (fun _ => 1) 2 (wordValid_sort N times ht)

/--
Exact identity `J.G N k = ∑ times ∈ (Finset.range N).powersetCard k, blockWord (fun a n =>
(2:ℝ)^n * J.blockBound a n) (fun _ => 1) N (times.sort (· ≥ ·))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem 4.3.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem G_eq_normalized_partitionBound (N k : ℕ) :
    J.G N k = ∑ times ∈ (Finset.range N).powersetCard k,
      blockWord (fun a n => (2:ℝ)^n * J.blockBound a n) (fun _ => 1) N (times.sort (· ≥ ·)) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  unfold G partitionBound
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro times ht
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
  rw [J.normalized_partitionWeight N times hsub, hcard]

end
end «2606.16671v2».JacobiData
