import chebyshev2.Green.Lift

/-!
Article: chebyshev2, Theorem A.1.
The grouped inverse identity of Theorem A.1.
Use: `chebyshev2.Jacobi.lift_green_odd` feeds `chebyshev2.Jacobi.lift_interval_room` (The
space between neighboring even sites accommodates length 1/d_i).
-/
namespace chebyshev2.Jacobi
noncomputable section
open Polynomial Polynomial.Chebyshev Matrix
open scoped Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Equation (109), including polynomial equality at x=0.

Exact identity `J.lift.matrix.charpoly = C ((1/2:ℝ)^N)*J.matrix.charpoly.comp (2*X^2-1)`.

Use: `chebyshev2.Jacobi.lift_terminal` rewrites with this identity to establish the precise
assertion is `J.lift.Terminal`.

Article: chebyshev2, Theorem A.1.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem lift_charpoly (h : (1+J.matrix).PosDef) :
    J.lift.matrix.charpoly = C ((1/2:ℝ)^N)*J.matrix.charpoly.comp (2*X^2-1) := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have he := Matrix.charpoly_reindex (Centering.interleave N).symm J.lift.matrix
  change (J.lift.matrix.submatrix (Centering.interleave N) (Centering.interleave N)).charpoly =
    J.lift.matrix.charpoly at he
  rw [← he, J.lift_grouped_matrix, Centering.blockLift_charpoly, J.cholesky_factor h]
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_pow, eval_X, eval_mul, eval_C, eval_sub, eval_ofNat,
    eval_one, Matrix.eval_charpoly]
  have hs : Matrix.scalar (Fin N) (x^2) - (1/2:ℝ) • (1+J.matrix) =
      (1/2:ℝ) • (Matrix.scalar (Fin N) (2*x^2-1)-J.matrix) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.diagonal, hij]; ring
  rw [hs, Matrix.det_smul, Fintype.card_fin]

/--
The precise assertion is `J.lift.Terminal`.

Use: `chebyshev2.centeringEquiv` uses this assertion in the displayed construction of
`centeringEquiv`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem A.1 via `chebyshev2.centeringEquiv`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem lift_terminal (hN : 0 < N) (ht : J.Terminal) : J.lift.Terminal := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [Terminal, chebyshev1.JacobiData.leading, J.lift.data.block_eq_charpoly J.lift.coupling_nonneg]
  change J.lift.matrix.charpoly = _
  rw [J.lift_charpoly (J.one_add_posDef hN ht), J.charpoly_eq ht,
    fiberPolynomial_eq N hN, fiberPolynomial_eq (2*N) (by omega), Polynomial.mul_comp,
    Polynomial.C_comp, ← T_two, ← T_mul]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [← mul_assoc, ← Polynomial.C_mul, Int.mul_comm (N:ℤ) 2]
  have hc : (1/2:ℝ)^N*(2/2^N) = 2/2^(2*N) := by
    rw [div_pow, one_pow, show 2*N = N+N by omega, pow_add]
    field_simp
  rw [hc]

/--
The grouped inverse identity of Theorem A.1.

Exact identity `J.lift.green.submatrix (Centering.interleave N) (Centering.interleave N) =
fromBlocks ((2:ℝ) • J.green) (((2:ℝ) • J.green)*J.cholesky) (J.choleskyᵀ*((2:ℝ) • J.green))
(1+J.choleskyᵀ*((2:ℝ) • J.green)*J.cholesky)`.

Use: `chebyshev2.Jacobi.lift_green_odd` uses this identity to establish the identity
`J.lift.green (Centering.interleave N (Sum.inl i)) (Centering.interleave N (Sum.inl j)) =
2*J.green i j`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_green_odd`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.cholesky_factor`,
`chebyshev2.Jacobi.lift_grouped_matrix`, `chebyshev2.Centering.blockLift_green` with
the arguments shown in the proof.
-/
theorem lift_grouped_green (h : (1+J.matrix).PosDef) (hm : (1-J.matrix).PosDef) :
    J.lift.green.submatrix (Centering.interleave N) (Centering.interleave N) =
      fromBlocks ((2:ℝ) • J.green) (((2:ℝ) • J.green)*J.cholesky)
        (J.choleskyᵀ*((2:ℝ) • J.green)) (1+J.choleskyᵀ*((2:ℝ) • J.green)*J.cholesky) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.cholesky_factor`,
  -- `chebyshev2.Jacobi.lift_grouped_matrix`, `chebyshev2.Centering.blockLift_green`
  -- with the arguments shown in the proof.
  have hs : 1-J.cholesky*J.choleskyᵀ = (1/2:ℝ) • (1-J.matrix) := by
    rw [J.cholesky_factor h]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hp : (1-J.cholesky*J.choleskyᵀ).PosDef := by
    rw [hs]; exact hm.smul (by norm_num)
  have hi : (1-J.cholesky*J.choleskyᵀ)⁻¹ = (2:ℝ) • J.green := by
    rw [hs]
    let := invertibleOfNonzero (by norm_num : (1/2:ℝ) ≠ 0)
    rw [Matrix.inv_smul (1-J.matrix) (1/2:ℝ) (isUnit_iff_ne_zero.mpr hm.det_pos.ne')]
    norm_num [green]
  rw [green, ← Matrix.inv_submatrix_equiv]
  simp only [Matrix.submatrix_sub, Pi.sub_apply]
  rw [Matrix.submatrix_one _ (Centering.interleave N).injective, J.lift_grouped_matrix,
    Centering.blockLift_green _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne'), hi]

/--
Exact identity `J.lift.green (Centering.interleave N (Sum.inl i)) (Centering.interleave N
(Sum.inl j)) = 2*J.green i j`.

Use: `chebyshev2.Jacobi.green_representation` rewrites with this identity to establish
exact identity `J.green i j = sqrt (J.green i i*J.green j j)* exp (-|J.representationPoint hN
i-J.representationPoint hN j|)`.

Article: chebyshev2, Theorem A.1.

Proof: Use the identities/estimates `chebyshev2.Jacobi.lift_grouped_green` with the
arguments shown in the proof.
-/
theorem lift_green_odd (h : (1+J.matrix).PosDef) (hm : (1-J.matrix).PosDef) (i j : Fin N) :
    J.lift.green (Centering.interleave N (Sum.inl i))
      (Centering.interleave N (Sum.inl j)) = 2*J.green i j := by
  have he := congrArg (fun A => A (Sum.inl i) (Sum.inl j)) (J.lift_grouped_green h hm)
  simpa using he

end
end chebyshev2.Jacobi
