import «2606.16671v2».Jacobi.InverseUniqueness
import «2606.16671v2».Spectral.Weights
import «2606.16671v2».Jacobi.Resolvent
import «2606.16671v2».Jacobi.ContinuantIdentities

/-!
Article: 2606.16671v2, Lemma E.5.
E.5, with the first spectral measure expressed by squared eigenvector coordinates.
Result: `«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights` supplies the stated article
conclusion.
Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — spectral weights of
finite Jacobi matrices. The needed form is proved here.
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) {n : ℕ}
variable (B : SpectralBasis (J.matrix 0 (n+1)))

/--
The endpoint cofactor formula for each spectral weight.

Exact identity `B.weight s j*(J.leading (n+1)).derivative.eval (B.eigenvalues j) = (J.leading
s.val).eval (B.eigenvalues j)* (J.block (s.val+1) (n-s.val)).eval (B.eigenvalues j)`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` uses this identity to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — spectral
weights of finite Jacobi matrices.

Proof: Use the identities/estimates
`«2606.16671v2».SpectralBasis.adjugate_eigenvalue_diagonal`,
`«2606.16671v2».JacobiData.block_eq_charpoly`, `«2606.16671v2».JacobiData.shifted_minor_det`
with the arguments shown in the proof.
-/
theorem spectral_weight_cofactor (hsq : ∀ t, 0 ≤ J.aSq t)
    (hi : Function.Injective B.eigenvalues) (s j : Fin (n+1)) :
    B.weight s j*(J.leading (n+1)).derivative.eval (B.eigenvalues j) =
      (J.leading s.val).eval (B.eigenvalues j)*
        (J.block (s.val+1) (n-s.val)).eval (B.eigenvalues j) := by
  -- Use the identities/estimates `«2606.16671v2».SpectralBasis.adjugate_eigenvalue_diagonal`,
  -- `«2606.16671v2».JacobiData.block_eq_charpoly`,
  -- `«2606.16671v2».JacobiData.shifted_minor_det` with the arguments shown in the proof.
  have he := B.adjugate_eigenvalue_diagonal hi s j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
    show s.val+s.val = 2*s.val by omega, pow_mul, neg_one_sq, one_pow, one_mul,
    J.shifted_minor_det n s _ hsq, ← J.block_eq_charpoly hsq] at he
  exact he.symm

/--
E.5's product identity follows from two diagonal cofactors and a continuant identity.

Exact identity `B.weight 0 j * B.weight (Fin.last n) j * ((J.leading (n+1)).derivative.eval
(B.eigenvalues j))^2 = J.couplingProduct 1 n`.

Use: `«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` uses this identity to
establish exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Article: 2606.16671v2, Lemma E.5.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — spectral
weights of finite Jacobi matrices.

Proof: Separate `n = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Check each member of the finite index type; no case is omitted.
-/
theorem spectral_endpoint_product (hsq : ∀ t, 0 ≤ J.aSq t)
    (hi : Function.Injective B.eigenvalues) (j : Fin (n+1)) :
    B.weight 0 j * B.weight (Fin.last n) j *
        ((J.leading (n+1)).derivative.eval (B.eigenvalues j))^2 = J.couplingProduct 1 n := by
  -- Separate `n = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hf := J.spectral_weight_cofactor B hsq hi 0 j
  have hl := J.spectral_weight_cofactor B hsq hi (Fin.last n) j
  simp only [Fin.val_zero, leading_zero, eval_one, one_mul, Nat.zero_add, Nat.sub_zero] at hf
  simp only [Fin.val_last, Nat.sub_self, block, eval_one, mul_one] at hl
  by_cases hn : n = 0
  · subst n
    fin_cases j
    have hw : B.weight 0 0 = 1 := by simpa using B.weight_sum 0
    simp [Fin.last_zero, hw, leading_one, couplingProduct]
  · have he := J.interior_identity (N := n+1) (a := 1) (by omega) (n-1) (by omega)
    have hr : (J.leading (n+1)).eval (B.eigenvalues j) = 0 := by
      rw [leading, J.block_eq_charpoly hsq, B.charpoly_factor, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    have hev := congrArg (eval (B.eigenvalues j)) he
    simp only [eval_mul, eval_sub, eval_C, hr, zero_mul] at hev
    rw [show 1+(n-1) = n by omega, show n+1-1 = n by omega,
      show n-1+1 = n by omega, show 1-1 = 0 by omega, Nat.sub_self, leading_zero, eval_one, block,
      eval_one, mul_one] at hev
    rw [← hf, ← hl] at hev
    linear_combination -hev

/--
The stated quantitative bound `0 < B.weight 0 j ∧ 0 < B.weight (Fin.last n) j`.

Use: `«2606.16671v2».JacobiData.spectral_weights_of_persymmetric` uses this bound to establish
establishes the uniform, quantified assertion `∀ j, B.weight 0 j = Real.sqrt (J.couplingProduct
1 n) / |(J.leading (n+1)).derivative.eval (B.eigenvalues j)|`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — spectral
weights of finite Jacobi matrices.

Proof: Use the identities/estimates `«2606.16671v2».SpectralBasis.weight_nonneg`,
`«2606.16671v2».JacobiData.spectral_endpoint_product` with the arguments shown in the proof.
-/
theorem spectral_endpoint_positive (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n+1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues) (j : Fin (n+1)) :
    0 < B.weight 0 j ∧ 0 < B.weight (Fin.last n) j := by
  -- Use the identities/estimates `«2606.16671v2».SpectralBasis.weight_nonneg`,
  -- `«2606.16671v2».JacobiData.spectral_endpoint_product` with the arguments shown in the
  -- proof.
  have hp : 0 < J.couplingProduct 1 n := by
    unfold couplingProduct
    exact Finset.prod_pos (fun s hs => hpos (1+s) (by omega) (by have := Finset.mem_range.mp hs; omega))
  rw [← J.spectral_endpoint_product B hsq hi j] at hp
  have h0 := B.weight_nonneg 0 j
  have h1 := B.weight_nonneg (Fin.last n) j
  have hd := sq_nonneg ((J.leading (n+1)).derivative.eval (B.eigenvalues j))
  constructor
  · apply lt_of_le_of_ne h0
    intro hz
    rw [← hz] at hp
    simp at hp
  · apply lt_of_le_of_ne h1
    intro hz
    rw [← hz] at hp
    simp at hp

/--
The inverse-spectral weight law for any persymmetric Jacobi matrix.

Establishes the uniform, quantified assertion `∀ j, B.weight 0 j = Real.sqrt (J.couplingProduct
1 n) / |(J.leading (n+1)).derivative.eval (B.eigenvalues j)|`.

Use: `«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights` uses this identity to
establish equivalence of the displayed criteria: `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev
= J.matrix 0 (n+1) ↔ ∃ c : ℝ, 0 < c ∧ ∀ j, B.weight 0 j = c/|(J.leading (n+1)).derivative.eval
(B.eigenvalues j)|`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — spectral
weights of finite Jacobi matrices.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly`,
`«2606.16671v2».JacobiData.matrix_principal_block`,
`«2606.16671v2».JacobiData.spectral_weight_cofactor` with the arguments shown in the proof.
-/
theorem spectral_weights_of_persymmetric (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n+1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues)
    (hrev : (J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)) :
    ∀ j, B.weight 0 j = Real.sqrt (J.couplingProduct 1 n) /
      |(J.leading (n+1)).derivative.eval (B.eigenvalues j)| := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.block_eq_charpoly`,
  -- `«2606.16671v2».JacobiData.matrix_principal_block`,
  -- `«2606.16671v2».JacobiData.spectral_weight_cofactor` with the arguments shown in the
  -- proof.
  have htail : J.block 1 n = J.leading n := by
    rw [leading, J.block_eq_charpoly hsq, J.block_eq_charpoly hsq]
    have hminor := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      M.submatrix Fin.castSucc Fin.castSucc) hrev
    have hmat : (J.matrix 1 n).submatrix Fin.rev Fin.rev = J.matrix 0 n := by
      rw [← J.matrix_principal_block (n+1) 1 n (by omega),
        ← J.matrix_principal_block (n+1) 0 n (by omega)]
      apply Matrix.ext
      intro i k
      have hm := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i k) hminor
      simp only [Matrix.submatrix_apply] at hm ⊢
      convert hm using 1 <;> congr 1 <;> apply Fin.ext <;> simp [Fin.rev] <;> omega
    have hc := Matrix.charpoly_reindex (Fin.revPerm : Fin n ≃ Fin n) (J.matrix 1 n)
    rw [show Matrix.reindex (Fin.revPerm : Fin n ≃ Fin n) Fin.revPerm (J.matrix 1 n) =
      J.matrix 0 n from hmat] at hc
    exact hc.symm
  intro j
  have hf := J.spectral_weight_cofactor B hsq hi 0 j
  have hl := J.spectral_weight_cofactor B hsq hi (Fin.last n) j
  simp only [Fin.val_zero, leading_zero, eval_one, one_mul, Nat.zero_add, Nat.sub_zero, htail] at hf
  simp only [Fin.val_last, Nat.sub_self, block, eval_one, mul_one] at hl
  have hd : (J.leading (n+1)).derivative.eval (B.eigenvalues j) ≠ 0 := by
    rw [leading, J.block_eq_charpoly hsq]
    exact B.charpoly_derivative_ne hi j
  have hw : B.weight (Fin.last n) j = B.weight 0 j :=
    mul_right_cancel₀ hd (hl.trans hf.symm)
  have hp := J.spectral_endpoint_product B hsq hi j
  rw [hw, show B.weight 0 j*B.weight 0 j*((J.leading (n+1)).derivative.eval (B.eigenvalues j))^2 =
    (B.weight 0 j*|(J.leading (n+1)).derivative.eval (B.eigenvalues j)|)^2 by rw [mul_pow, sq_abs]; ring] at hp
  have hwpos := (J.spectral_endpoint_positive B hsq hpos hi j).1
  have hs := congrArg Real.sqrt hp
  rw [Real.sqrt_sq (mul_nonneg hwpos.le (abs_nonneg _))] at hs
  exact (eq_div_iff (abs_ne_zero.mpr hd)).mpr hs


/--
The converse inverse-spectral criterion in E.5. The proof recovers the Jacobi recurrence from
its two endpoint cofactors rather than assuming uniqueness.

Exact identity `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1)`.

Use: `«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights` uses this identity to
establish equivalence of the displayed criteria: `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev
= J.matrix 0 (n+1) ↔ ∃ c : ℝ, 0 < c ∧ ∀ j, B.weight 0 j = c/|(J.leading (n+1)).derivative.eval
(B.eigenvalues j)|`.

Article: 2606.16671v2, Lemma E.5 via
`«2606.16671v2».JacobiData.persymmetric_iff_spectral_weights`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — spectral
weights of finite Jacobi matrices.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem persymmetric_of_spectral_weights (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n+1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues) (c : ℝ) (hc : 0 < c)
    (hw : ∀ j, B.weight 0 j = c/|(J.leading (n+1)).derivative.eval (B.eigenvalues j)|) :
    (J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let r := J.couplingProduct 1 n/c^2
  have hd (j : Fin (n+1)) : (J.leading (n+1)).derivative.eval (B.eigenvalues j) ≠ 0 := by
    rw [leading, J.block_eq_charpoly hsq]
    exact B.charpoly_derivative_ne hi j
  have hlast (j : Fin (n+1)) : B.weight (Fin.last n) j = r*B.weight 0 j := by
    have hp := J.spectral_endpoint_product B hsq hi j
    rw [hw j] at hp ⊢
    have hsqabs := sq_abs ((J.leading (n+1)).derivative.eval (B.eigenvalues j))
    rw [← hsqabs] at hp
    dsimp [r]
    field_simp [ne_of_gt hc, abs_ne_zero.mpr (hd j)] at hp ⊢
    nlinarith
  have hr : r = 1 := by
    have hh := B.weight_sum (Fin.last n)
    simp_rw [hlast] at hh
    rw [← Finset.mul_sum, B.weight_sum 0, mul_one] at hh
    exact hh
  apply J.persymmetric_of_endpoint_blocks hsq hpos
  apply eq_of_natDegree_lt_card_of_eval_eq _ _ hi
  · intro j
    have hf := J.spectral_weight_cofactor B hsq hi 0 j
    have hl := J.spectral_weight_cofactor B hsq hi (Fin.last n) j
    simp only [Fin.val_zero, leading_zero, eval_one, one_mul, Nat.zero_add, Nat.sub_zero] at hf
    simp only [Fin.val_last, Nat.sub_self, block, eval_one, mul_one] at hl
    rw [hlast, hr, one_mul] at hl
    exact hf.symm.trans hl
  · simp only [leading, J.block_natDegree hsq, max_self, Fintype.card_fin]
    omega

/--
E.5, with the first spectral measure expressed by squared eigenvector coordinates.

Equivalence of the displayed criteria: `(J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix
0 (n+1) ↔ ∃ c : ℝ, 0 < c ∧ ∀ j, B.weight 0 j = c/|(J.leading (n+1)).derivative.eval
(B.eigenvalues j)|`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Lemma E.5.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — spectral
weights of finite Jacobi matrices.

Proof: Use the identities/estimates
`«2606.16671v2».JacobiData.spectral_weights_of_persymmetric`,
`«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` with the arguments shown in the
proof.
-/
theorem persymmetric_iff_spectral_weights (hsq : ∀ t, 0 ≤ J.aSq t)
    (hpos : ∀ s, 0 < s → s < n+1 → 0 < J.aSq s)
    (hi : Function.Injective B.eigenvalues) :
    (J.matrix 0 (n+1)).submatrix Fin.rev Fin.rev = J.matrix 0 (n+1) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ j, B.weight 0 j =
        c/|(J.leading (n+1)).derivative.eval (B.eigenvalues j)| := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.spectral_weights_of_persymmetric`,
  -- `«2606.16671v2».JacobiData.persymmetric_of_spectral_weights` with the arguments shown in
  -- the proof.
  constructor
  · intro hrev
    refine ⟨Real.sqrt (J.couplingProduct 1 n), ?_,
      J.spectral_weights_of_persymmetric B hsq hpos hi hrev⟩
    apply Real.sqrt_pos.mpr
    unfold couplingProduct
    exact Finset.prod_pos (fun s hs => hpos (1+s) (by omega) (by have := Finset.mem_range.mp hs; omega))
  · rintro ⟨c,hc,hw⟩
    exact J.persymmetric_of_spectral_weights B hsq hpos hi c hc hw

end
end «2606.16671v2».JacobiData
