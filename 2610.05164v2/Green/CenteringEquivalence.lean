import «2610.05164v2».Green.Decomposition
import «2610.05164v2».Finite.MatrixExt

/-!
Article: 2610.05164v2, Theorem A.1.
The fiber bijection of Theorem A.1, with its explicit compression inverse.
Result: `«2610.05164v2».centeringEquiv` supplies the stated article conclusion.
-/
namespace «2610.05164v2»
noncomputable section
open Polynomial Polynomial.Chebyshev

/--
Exact identity `fiberPolynomial (2*N) = C ((1/2:ℝ)^N)*(fiberPolynomial N).comp (2*X^2-1)`.

Use: `«2610.05164v2».Centering.compression_terminal` rewrites with this identity to establish
the precise assertion is `(compression C).Terminal`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem fiberPolynomial_double (N : ℕ) (hN : 0 < N) :
    fiberPolynomial (2*N) = C ((1/2:ℝ)^N)*(fiberPolynomial N).comp (2*X^2-1) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [fiberPolynomial_eq N hN, fiberPolynomial_eq (2*N) (by omega), Polynomial.mul_comp,
    Polynomial.C_comp, ← T_two, ← T_mul]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [← mul_assoc, ← Polynomial.C_mul, Int.mul_comm (N:ℤ) 2]
  congr 1
  rw [div_pow, one_pow, show 2*N = N+N by omega, pow_add]
  field_simp

/--
Defines `IrreducibleFiber` of type `(N : ℕ)` by `{J : Jacobi N // J.Terminal ∧ J.Irreducible}`.

Use: `«2610.05164v2».centeringEquiv` uses this definition in the displayed construction of
`centeringEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.
-/
abbrev IrreducibleFiber (N : ℕ) := {J : Jacobi N // J.Terminal ∧ J.Irreducible}
/--
Defines `CenteredFiber` of type `(N : ℕ)` by `{J : Jacobi N // J.Terminal ∧ J.Centered}`.

Use: `«2610.05164v2».centeringEquiv` uses this definition in the displayed construction of
`centeringEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.
-/
abbrev CenteredFiber (N : ℕ) := {J : Jacobi N // J.Terminal ∧ J.Centered}

namespace Centering
open Matrix Real
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (C : Jacobi (2*N))

/--
The precise assertion is `(compression C).Terminal`.

Use: `«2610.05164v2».Centering.extractedBlock_is_cholesky` uses this assertion to establish
exact identity `extractedBlock C = (compression C).cholesky`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.charpoly_eq`,
`«2610.05164v2».fiberPolynomial_double`, `«2610.05164v2».Centering.charpoly_compression` with
the arguments shown in the proof.
-/
theorem compression_terminal (hN : 0 < N) (ht : C.Terminal) (hc : C.Centered) :
    (compression C).Terminal := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.charpoly_eq`,
  -- `«2610.05164v2».fiberPolynomial_double`, `«2610.05164v2».Centering.charpoly_compression`
  -- with the arguments shown in the proof.
  have he := C.charpoly_eq ht
  rw [charpoly_compression C hc, fiberPolynomial_double N hN] at he
  have he := mul_left_cancel₀ (show Polynomial.C ((1/2:ℝ)^N) ≠ 0 by simp) he
  have hp : (compression C).matrix.charpoly = fiberPolynomial N := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Ioi_infinite (-1:ℝ)).mono
    intro y hy
    change Polynomial.eval y (compression C).matrix.charpoly = Polynomial.eval y (fiberPolynomial N)
    let x : ℝ := sqrt ((y+1)/2)
    have hx : 2*x^2-1 = y := by
      have hs := sq_sqrt (show 0 ≤ (y+1)/2 by simp only [Set.mem_Ioi] at hy; linarith)
      dsimp [x]; linarith
    have hh := congrArg (Polynomial.eval x) he
    simpa only [eval_comp, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X, eval_one, hx] using hh
  rw [Jacobi.Terminal, «2606.16671v2».JacobiData.leading, (compression C).data.block_eq_charpoly
    (compression C).coupling_nonneg]
  exact hp

/--
Exact identity `extractedBlock C = (compression C).cholesky`.

Use: `«2610.05164v2».Centering.lift_compression` rewrites with this identity to establish exact
identity `(compression C).lift = C`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Centering.compression_matrix`,
`«2610.05164v2».Jacobi.one_add_posDef`, `«2610.05164v2».Centering.compression_terminal` with
the arguments shown in the proof.
-/
theorem extractedBlock_is_cholesky (hN : 0 < N) (ht : C.Terminal) (hc : C.Centered) :
    extractedBlock C = (compression C).cholesky := by
  -- Use the identities/estimates `«2610.05164v2».Centering.compression_matrix`,
  -- `«2610.05164v2».Jacobi.one_add_posDef`, `«2610.05164v2».Centering.compression_terminal`
  -- with the arguments shown in the proof.
  have hf : extractedBlock C*(extractedBlock C)ᵀ = (1/2:ℝ) • (1+(compression C).matrix) := by
    rw [compression_matrix C]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hp := (compression C).one_add_posDef hN (compression_terminal C hN ht hc)
  obtain ⟨hd,hl⟩ := (compression C).cholesky_unique hp (diagonal C) (lower C)
    (diagonal_pos C hc) (lower_zero C) hf
  rw [extractedBlock, hd, hl]
  rfl

/--
Exact identity `(compression C).lift = C`.

Use: `«2610.05164v2».centeringEquiv` uses this identity in the displayed construction of
`centeringEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_injective`,
`«2610.05164v2».Jacobi.lift_grouped_matrix`, `«2610.05164v2».Centering.grouped_matrix` with the
arguments shown in the proof.
-/
theorem lift_compression (hN : 0 < N) (ht : C.Terminal) (hc : C.Centered) :
    (compression C).lift = C := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.matrix_injective`,
  -- `«2610.05164v2».Jacobi.lift_grouped_matrix`, `«2610.05164v2».Centering.grouped_matrix`
  -- with the arguments shown in the proof.
  apply Jacobi.matrix_injective
  have he : (compression C).lift.matrix.submatrix (interleave N) (interleave N) =
      C.matrix.submatrix (interleave N) (interleave N) := by
    rw [(compression C).lift_grouped_matrix, grouped_matrix C hc,
      extractedBlock_is_cholesky C hN ht hc]
  ext i j
  have hh := congrArg (fun A => A ((interleave N).symm i) ((interleave N).symm j)) he
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using hh

end Centering

namespace Jacobi
open Matrix Real
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Exact identity `Centering.extractedBlock J.lift = J.cholesky`.

Use: `«2610.05164v2».Jacobi.compression_lift` rewrites with this identity to establish exact
identity `Centering.compression J.lift = J`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Separate `0 < i.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem extractedBlock_lift : Centering.extractedBlock J.lift = J.cholesky := by
  -- Separate `0 < i.val` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hd : Centering.diagonal J.lift = J.choleskyDiagonal := by
    funext i
    rw [Centering.diagonal, J.lift_odd_coupling]
    exact sqrt_sq (sqrt_nonneg _)
  have hl : Centering.lower J.lift = J.choleskyLower := by
    funext i
    rw [Centering.lower, J.lift_even_coupling]
    by_cases hi : 0 < i.val
    · rw [ite_eq_left hi]; exact sqrt_sq (sqrt_nonneg _)
    · have hi0 : i.val = 0 := by omega
      rw [ite_eq_right hi, sqrt_zero, J.choleskyLower_zero i hi0]
  rw [Centering.extractedBlock, hd, hl]
  rfl

/--
Exact identity `Centering.compression J.lift = J`.

Use: `«2610.05164v2».centeringEquiv` uses this identity in the displayed construction of
`centeringEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».centeringEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.matrix_injective`,
`«2610.05164v2».Centering.compression_matrix`, `«2610.05164v2».Jacobi.extractedBlock_lift` with
the arguments shown in the proof.
-/
theorem compression_lift (h : (1+J.matrix).PosDef) : Centering.compression J.lift = J := by
  apply matrix_injective
  rw [Centering.compression_matrix, J.extractedBlock_lift, J.cholesky_factor h]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

end Jacobi

/--
The fiber bijection of Theorem A.1, with its explicit compression inverse.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem A.1.
-/
def centeringEquiv (N : ℕ) (hN : 0 < N) : IrreducibleFiber N ≃ CenteredFiber (2*N) where
  toFun J := ⟨J.val.lift, J.val.lift_terminal hN J.property.1,
    J.val.lift_centered (J.val.one_add_posDef hN J.property.1) J.property.2⟩
  invFun C := ⟨Centering.compression C.val,
    Centering.compression_terminal C.val hN C.property.1 C.property.2,
    Centering.compression_irreducible C.val C.property.2⟩
  left_inv J := Subtype.ext (J.val.compression_lift (J.val.one_add_posDef hN J.property.1))
  right_inv C := Subtype.ext (Centering.lift_compression C.val hN C.property.1 C.property.2)

end
end «2610.05164v2»
