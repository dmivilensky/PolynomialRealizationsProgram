import «2606.16671v2».Jacobi.ContinuantIdentities
import «2606.16671v2».Jacobi.Determinant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
Article: 2606.16671v2, Lemma E.5.
Equality of the two endpoint cofactors characterizes reversal symmetry.
Use: `«2606.16671v2».JacobiData.persymmetric_of_endpoint_blocks` feeds
`«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` (The converse inverse-spectral
criterion in E.5).
Proof chain: `«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights` — 2606.16671v2, Lemma
E.5; Persymmetric inverse-spectral criterion.
Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction. The needed form is proved here.
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

variable (J K : JacobiData)

/--
The precise assertion is `(J.block a n).Monic`.

Use: `«2606.16671v2».JacobiData.block_coeff_top` uses this assertion to establish exact
identity `(J.block a n).coeff n = 1`.

Article: 2606.16671v2, Lemma E.5 via `«2606.16671v2».JacobiData.block_pair_unique`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly` with the
arguments shown in the proof.
-/
theorem block_monic (hsq : ∀ t, 0 ≤ J.aSq t) (a n : ℕ) : (J.block a n).Monic := by
  rw [J.block_eq_charpoly hsq]
  exact Matrix.charpoly_monic _

/--
Exact identity `(J.block a n).natDegree = n`.

Use: `«2606.16671v2».JacobiData.block_coeff_top` uses this identity to establish the identity
`(J.block a n).coeff n = 1`.

Article: 2606.16671v2, Lemma E.5 via `«2606.16671v2».JacobiData.block_pair_unique`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly` with the
arguments shown in the proof.
-/
theorem block_natDegree (hsq : ∀ t, 0 ≤ J.aSq t) (a n : ℕ) : (J.block a n).natDegree = n := by
  rw [J.block_eq_charpoly hsq, Matrix.charpoly_natDegree_eq_dim]
  simp

/--
Exact identity `(J.block a n).coeff n = 1`.

Use: `«2606.16671v2».JacobiData.block_pair_unique` rewrites with this identity to establish
exact identity `(∀ i ≤ n, J.b (a+i) = K.b (b+i)) ∧ (∀ i, 0 < i → i ≤ n → J.aSq (a+i) = K.aSq
(b+i))`.

Article: 2606.16671v2, Lemma E.5 via `«2606.16671v2».JacobiData.block_pair_unique`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_natDegree`,
`«2606.16671v2».JacobiData.block_monic` with the arguments shown in the proof.
-/
theorem block_coeff_top (hsq : ∀ t, 0 ≤ J.aSq t) (a n : ℕ) : (J.block a n).coeff n = 1 := by simpa only [J.block_natDegree hsq] using (J.block_monic hsq a n).coeff_natDegree

/--
The first two characteristic polynomials uniquely recover a finite Jacobi block. The positivity
of the couplings fixes the orientation of the recurrence.

Exact identity `(∀ i ≤ n, J.b (a+i) = K.b (b+i)) ∧ (∀ i, 0 < i → i ≤ n → J.aSq (a+i) = K.aSq
(b+i))`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_endpoint_blocks` uses this identity to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Induct on `n` while keeping `a b` arbitrary; the recursive step uses the
previous-stage assertion. Separate `i = 0` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem block_pair_unique (hJ : ∀ t, 0 ≤ J.aSq t) (hK : ∀ t, 0 ≤ K.aSq t)
    (n a b : ℕ) (hp : ∀ s, 0 < s → s ≤ n → 0 < J.aSq (a+s))
    (he : J.block a (n+1) = K.block b (n+1))
    (ht : J.block (a+1) n = K.block (b+1) n) :
    (∀ i ≤ n, J.b (a+i) = K.b (b+i)) ∧
    (∀ i, 0 < i → i ≤ n → J.aSq (a+i) = K.aSq (b+i)) := by
  -- Induct on `n` while keeping `a b` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction n generalizing a b with
  | zero =>
    have hb : J.b a = K.b b := by
      have hh := congrArg (fun p : ℝ[X] => p.coeff 0) he
      simpa [block] using hh
    constructor
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simpa using hb
    · intro i hi hiN; omega
  | succ n ih =>
    have hrecJ := J.block_left a n
    have hrecK := K.block_left b n
    rw [ht] at hrecJ
    have hrel : C (K.b b-J.b a)*K.block (b+1) (n+1) =
        C (J.aSq (a+1))*J.block (a+2) n-C (K.aSq (b+1))*K.block (b+2) n := by
      rw [show n+1+1 = n+2 by omega] at he
      rw [C_sub]
      linear_combination hrecK-hrecJ+he
    have hb : J.b a = K.b b := by
      have hh := congrArg (fun p : ℝ[X] => p.coeff (n+1)) hrel
      have hj0 : (J.block (a+2) n).coeff (n+1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [J.block_natDegree hJ]; omega)
      have hk0 : (K.block (b+2) n).coeff (n+1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [K.block_natDegree hK]; omega)
      simp only [coeff_C_mul, coeff_sub, K.block_coeff_top hK, hj0, hk0, mul_one,
        mul_zero, sub_zero] at hh
      linarith
    have he2 : C (J.aSq (a+1))*J.block (a+2) n = C (K.aSq (b+1))*K.block (b+2) n := by
      rw [hb, sub_self, C_0, zero_mul] at hrel
      exact sub_eq_zero.mp hrel.symm
    have hc : J.aSq (a+1) = K.aSq (b+1) := by
      have hh := congrArg (fun p : ℝ[X] => p.coeff n) he2
      simpa only [coeff_C_mul, J.block_coeff_top hJ, K.block_coeff_top hK, mul_one] using hh
    have hrest : J.block (a+2) n = K.block (b+2) n := by
      rw [← hc] at he2
      exact mul_left_cancel₀ (C_ne_zero.mpr (ne_of_gt (hp 1 (by omega) (by omega)))) he2
    have hr := ih (a+1) (b+1) (fun s hs hsN => by
      convert hp (s+1) (by omega) (by omega) using 1
      congr 1
      omega) ht (by
        simpa only [Nat.add_assoc] using hrest)
    constructor
    · intro i hi
      by_cases h0 : i = 0
      · subst i; simpa using hb
      · have hh := hr.1 (i-1) (by omega)
        simpa only [show a+1+(i-1) = a+i by omega, show b+1+(i-1) = b+i by omega] using hh
    · intro i hi hiN
      by_cases h1 : i = 1
      · subst i; exact hc
      · have hh := hr.2 (i-1) (by omega) (by omega)
        simpa only [show a+1+(i-1) = a+i by omega, show b+1+(i-1) = b+i by omega] using hh

/--
Reversal is extended harmlessly beyond its finite horizon.

Use: `«2606.16671v2».JacobiData.persymmetric_of_endpoint_blocks` uses this definition to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5 via
`«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.
-/
def reversed (N : ℕ) : JacobiData where
  b := fun s => J.b (N-1-s)
  aSq := fun s => if s ≤ N then J.aSq (N-s) else 0

/--
The stated quantitative bound `0 ≤ (J.reversed N).aSq t`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_endpoint_blocks` uses this bound to establish
exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5 via
`«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem reversed_aSq_nonneg (hsq : ∀ t, 0 ≤ J.aSq t) (N t : ℕ) : 0 ≤ (J.reversed N).aSq t := by
  dsimp [reversed]
  split_ifs
  · exact hsq _
  · rfl

/--
Exact identity `(J.reversed N).matrix a n = (J.matrix (N-a-n) n).submatrix Fin.rev Fin.rev`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_endpoint_blocks` uses this identity to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5 via
`«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.matrix_apply` with the arguments
shown in the proof.
-/
theorem reversed_matrix (N a n : ℕ) (hn : a+n ≤ N) :
    (J.reversed N).matrix a n = (J.matrix (N-a-n) n).submatrix Fin.rev Fin.rev := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.matrix_apply` with the arguments
  -- shown in the proof.
  apply Matrix.ext
  intro i k
  rw [Matrix.submatrix_apply, matrix_apply, matrix_apply]
  simp only [reversed]
  have hdiag : i.rev = k.rev ↔ i = k := Fin.rev_injective.eq_iff
  have h1 : i.rev.val+1 = k.rev.val ↔ k.val+1 = i.val := by dsimp [Fin.rev]; omega
  have h2 : k.rev.val+1 = i.rev.val ↔ i.val+1 = k.val := by dsimp [Fin.rev]; omega
  simp only [hdiag, h1, h2]
  split_ifs <;> first | congr 2; dsimp [Fin.rev]; omega | omega | rfl

/--
Exact identity `(J.reversed N).block a n = J.block (N-a-n) n`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_endpoint_blocks` rewrites with this identity to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5 via
`«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly`,
`«2606.16671v2».JacobiData.reversed_aSq_nonneg`, `«2606.16671v2».JacobiData.reversed_matrix`
with the arguments shown in the proof.
-/
theorem reversed_block (hsq : ∀ t, 0 ≤ J.aSq t) (N a n : ℕ) (hn : a+n ≤ N) :
    (J.reversed N).block a n = J.block (N-a-n) n := by
  rw [block_eq_charpoly _ (J.reversed_aSq_nonneg hsq N), reversed_matrix _ N a n hn,
    J.block_eq_charpoly hsq]
  exact Matrix.charpoly_reindex (Fin.revPerm : Fin n ≃ Fin n) (J.matrix (N-a-n) n)

/--
Equality of the two endpoint cofactors characterizes reversal symmetry.

Exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` uses this identity to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5 via
`«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — finite Jacobi
inverse spectral reconstruction.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_pair_unique`,
`«2606.16671v2».JacobiData.reversed_aSq_nonneg`, `«2606.16671v2».JacobiData.reversed_block`
with the arguments shown in the proof.
-/
theorem persymmetric_of_endpoint_blocks {n : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n+1 → 0 < J.aSq s)
    (he : J.block 1 n = J.leading n) :
    (J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1) := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.block_pair_unique`,
  -- `«2606.16671v2».JacobiData.reversed_aSq_nonneg`,
  -- `«2606.16671v2».JacobiData.reversed_block` with the arguments shown in the proof.
  have hp := J.block_pair_unique (J.reversed (n+1)) hsq (J.reversed_aSq_nonneg hsq (n+1)) n 0 0
    (fun s hs hsN => by simpa using hpos s hs (by omega))
    (by rw [J.reversed_block hsq (n+1) 0 (n+1) (by omega)]; simp)
    (by rw [J.reversed_block hsq (n+1) 1 n (by omega)]; simpa [leading] using he)
  have hrev := J.reversed_matrix (n+1) 0 (n+1) (by omega)
  simp only [Nat.sub_zero, Nat.sub_self] at hrev
  rw [← hrev]
  apply Matrix.ext
  intro i k
  rw [matrix_apply, matrix_apply]
  have hb : ∀ s < n+1, (J.reversed (n+1)).b s = J.b s := by
    intro s hs; simpa using (hp.1 s (by omega)).symm
  have hc : ∀ s, 0 < s → s < n+1 → (J.reversed (n+1)).aSq s = J.aSq s := by
    intro s hs hsN; simpa using (hp.2 s hs (by omega)).symm
  simp only [Nat.zero_add]
  split_ifs <;> first | rw [hb _ i.isLt] | rw [hc _ (by omega) k.isLt] | rw [hc _ (by omega) i.isLt] | rfl

end
end «2606.16671v2».JacobiData
