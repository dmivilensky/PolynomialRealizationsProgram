import chebyshev2.Green.Cholesky
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Article: chebyshev2, Theorem A.1.
The actual inverse of the lifted pencil.
Use: `chebyshev2.Centering.blockLift_green` feeds `chebyshev2.Jacobi.lift_grouped_green`
(The grouped inverse identity of Theorem A.1).
Proof chain: `chebyshev2.Jacobi.lift_green_odd` — chebyshev2, Theorem A.1; Centering lift,
contractivity, odd Green entries and characteristic polynomial.
-/
namespace chebyshev2.Centering
noncomputable section
open Polynomial Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/--
Defines `blockLift` of type `Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ` by `fromBlocks 0 B Bᵀ
0`.

Use: `chebyshev2.Centering.blockLift_pencil` rewrites with this definition to establish
exact identity `x • 1-blockLift B = fromBlocks (x • 1) (-B) (-Bᵀ) (x • 1)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_grouped_matrix`.
-/
def blockLift (B : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ := fromBlocks 0 B Bᵀ 0

/--
Exact identity `x • 1-blockLift B = fromBlocks (x • 1) (-B) (-Bᵀ) (x • 1)`.

Use: `chebyshev2.Centering.blockLift_charpoly` rewrites with this identity to establish
exact identity `(blockLift B).charpoly = (B*Bᵀ).charpoly.comp (X^2)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_charpoly`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem blockLift_pencil (B : Matrix (Fin N) (Fin N) ℝ) (x : ℝ) :
    x • 1-blockLift B = fromBlocks (x • 1) (-B) (-Bᵀ) (x • 1) := by ext i j; cases i <;> cases j <;> simp [blockLift, Matrix.one_apply, fromBlocks]

/--
The block determinant identity, as an equality of characteristic polynomials.

Exact identity `(blockLift B).charpoly = (B*Bᵀ).charpoly.comp (X^2)`.

Use: `chebyshev2.Centering.blockLift_affine_charpoly` rewrites with this identity to
establish exact identity `(blockLift B).charpoly = C ((1/2:ℝ)^N)*((2:ℝ) •
(B*Bᵀ)-1).charpoly.comp (2*X^2-1)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_charpoly`.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem blockLift_charpoly (B : Matrix (Fin N) (Fin N) ℝ) :
    (blockLift B).charpoly = (B*Bᵀ).charpoly.comp (X^2) := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_univ.sdiff (Set.finite_singleton (0:ℝ))).mono
  intro x hx
  have hx0 : x ≠ 0 := hx.2
  have hd : IsUnit (x • (1 : Matrix (Fin N) (Fin N) ℝ)).det := by
    rw [det_smul]; simp [hx0]
  let := Matrix.invertibleOfIsUnitDet (x • (1 : Matrix (Fin N) (Fin N) ℝ)) hd
  have hi : ⅟(x • (1 : Matrix (Fin N) (Fin N) ℝ)) = x⁻¹ • 1 := by
    rw [invOf_eq_nonsing_inv]
    apply inv_eq_left_inv
    simp [smul_smul, hx0]
  have hs : x • (1 : Matrix (Fin N) (Fin N) ℝ) - (-B)*(x⁻¹ • 1)*(-Bᵀ) =
      x⁻¹ • (x^2 • 1-B*Bᵀ) := by
    simp only [mul_neg, neg_mul, mul_smul_comm, mul_one, smul_mul_assoc]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
    field_simp [hx0]
  simp only [Set.mem_ofPred_eq, eval_comp, eval_pow, eval_X, Matrix.eval_charpoly]
  have hscalar {k : Type} [DecidableEq k] [Fintype k] (t : ℝ) : Matrix.scalar k t = t • 1 := by
    ext i j; by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.diagonal, hij]
  rw [hscalar, hscalar]
  rw [blockLift_pencil, det_fromBlocks₂₂, hi, hs, det_smul, det_smul, det_one,
    mul_one, Fintype.card_fin]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0, one_pow, one_mul]

/--
The actual inverse of the lifted pencil. Its upper-left block is the Schur inverse.

Exact identity `(blockLift B).charpoly = C ((1/2:ℝ)^N)*((2:ℝ) • (B*Bᵀ)-1).charpoly.comp
(2*X^2-1)`.

Use: `chebyshev2.Centering.charpoly_compression` rewrites with this identity to establish
exact identity `C.matrix.charpoly = Polynomial.C ((1/2:ℝ)^N)*(compression
C).matrix.charpoly.comp (2*Polynomial.X^2-1)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.centeringEquiv`.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem blockLift_affine_charpoly (B : Matrix (Fin N) (Fin N) ℝ) :
    (blockLift B).charpoly = C ((1/2:ℝ)^N)*((2:ℝ) • (B*Bᵀ)-1).charpoly.comp (2*X^2-1) := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [blockLift_charpoly]
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_pow, eval_X, eval_mul, eval_C, eval_sub, eval_ofNat,
    eval_one, Matrix.eval_charpoly]
  have hs : Matrix.scalar (Fin N) (x^2)-B*Bᵀ =
      (1/2:ℝ) • (Matrix.scalar (Fin N) (2*x^2-1)-((2:ℝ) • (B*Bᵀ)-1)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.diagonal, hij]; ring
  rw [hs, Matrix.det_smul, Fintype.card_fin]

/--
The actual inverse of the lifted pencil. Its upper-left block is the Schur inverse.

Exact identity `(1-blockLift B)⁻¹ = fromBlocks (1-B*Bᵀ)⁻¹ ((1-B*Bᵀ)⁻¹*B) (Bᵀ*(1-B*Bᵀ)⁻¹)
(1+Bᵀ*(1-B*Bᵀ)⁻¹*B)`.

Use: `chebyshev2.Jacobi.lift_grouped_green` rewrites with this identity to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_green_odd`.

Proof: Use the identities/estimates `chebyshev2.Centering.blockLift_pencil` with the
arguments shown in the proof.
-/
theorem blockLift_green (B : Matrix (Fin N) (Fin N) ℝ)
    (h : IsUnit (1-B*Bᵀ).det) :
    (1-blockLift B)⁻¹ =
      fromBlocks (1-B*Bᵀ)⁻¹ ((1-B*Bᵀ)⁻¹*B)
        (Bᵀ*(1-B*Bᵀ)⁻¹) (1+Bᵀ*(1-B*Bᵀ)⁻¹*B) := by
  -- Use the identities/estimates `chebyshev2.Centering.blockLift_pencil` with the
  -- arguments shown in the proof.
  rw [show (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) = (1:ℝ) • 1 by simp,
    blockLift_pencil]
  apply inv_eq_left_inv
  rw [fromBlocks_multiply]
  simp only [one_smul]
  have he := nonsing_inv_mul _ h
  have htl : (1-B*Bᵀ)⁻¹*1 + ((1-B*Bᵀ)⁻¹*B)*(-Bᵀ) = 1 := by
    convert he using 1; noncomm_ring
  have hbl : (Bᵀ*(1-B*Bᵀ)⁻¹)*1 + (1+Bᵀ*(1-B*Bᵀ)⁻¹*B)*(-Bᵀ) = 0 := by
    have hh := congrArg (fun A => Bᵀ*A) he
    simp only [mul_one] at hh
    calc
      _ = Bᵀ*((1-B*Bᵀ)⁻¹*(1-B*Bᵀ))-Bᵀ := by noncomm_ring
      _ = 0 := by rw [hh]; simp
  rw [htl, hbl]
  convert fromBlocks_one using 1; noncomm_ring

end
end chebyshev2.Centering
