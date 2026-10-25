import chebyshev2.Green.Bidiagonal
import chebyshev2.Green.Positivity

/-!
Article: chebyshev2, Proposition 1.
Uniqueness of the factor, including its finite coefficient representation.
Use: `chebyshev2.Jacobi.cholesky_unique` feeds
`chebyshev2.Centering.extractedBlock_is_cholesky` (extracted Block is cholesky).
Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal matrices —
tridiagonal inverse factorization. The needed form is proved here.
-/
namespace chebyshev2.Jacobi
noncomputable section
open chebyshev1 Polynomial Real
open scoped BigOperators Matrix
variable {N : ℕ} (J : Jacobi N)

/--
The leading principal determinant of I+J.

Use: `chebyshev2.Jacobi.choleskyDiagonal` uses this definition in the displayed
construction of `choleskyDiagonal`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_grouped_matrix`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.
-/
def positiveMinor (n : ℕ) : ℝ := (-1)^n*(J.data.leading n).eval (-1)

/--
Exact identity `J.positiveMinor n = (1+J.data.matrix 0 n).det`.

Use: `chebyshev2.Jacobi.positiveMinor_pos` rewrites with this identity to establish the
stated quantitative bound `0 < J.positiveMinor n`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem positiveMinor_eq_det (n : ℕ) :
    J.positiveMinor n = (1+J.data.matrix 0 n).det := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [positiveMinor, JacobiData.leading, J.data.block_eq_charpoly J.coupling_nonneg,
    Matrix.eval_charpoly]
  have hs : Matrix.scalar (Fin n) (-1:ℝ) = -1 := by
    ext i j; by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.diagonal, hij]
  rw [hs, show (-1-J.data.matrix 0 n) = -(1+J.data.matrix 0 n) by abel,
    Matrix.det_neg, Fintype.card_fin]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/--
Exact identity `J.positiveMinor 0 = 1`.

Use: `chebyshev2.Jacobi.choleskyLower_zero` uses this identity to establish the identity
`J.choleskyLower i = 0`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem positiveMinor_zero : J.positiveMinor 0 = 1 := by simp [positiveMinor]
/--
Exact identity `J.positiveMinor 1 = 1+J.data.b 0`.

Use: `chebyshev2.Jacobi.cholesky_diagonal_identity` rewrites with this identity to
establish exact identity `J.choleskyDiagonal i^2 + (if 0 < i.val then J.choleskyLower i^2 else
0) = (1+J.data.b i.val)/2`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem positiveMinor_one : J.positiveMinor 1 = 1+J.data.b 0 := by simp [positiveMinor]; ring

/--
Exact identity `J.positiveMinor (n+2) = (1+J.data.b (n+1))*J.positiveMinor (n+1) - J.data.aSq
(n+1)*J.positiveMinor n`.

Use: `chebyshev2.Jacobi.cholesky_diagonal_identity` uses this identity to establish exact
identity `J.choleskyDiagonal i^2 + (if 0 < i.val then J.choleskyLower i^2 else 0) = (1+J.data.b
i.val)/2`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Use the identities/estimates `chebyshev1.JacobiData.leading_add_two` with the
arguments shown in the proof.
-/
theorem positiveMinor_recurrence (n : ℕ) :
    J.positiveMinor (n+2) = (1+J.data.b (n+1))*J.positiveMinor (n+1) -
      J.data.aSq (n+1)*J.positiveMinor n := by
  rw [positiveMinor, J.data.leading_add_two]
  simp only [eval_sub, eval_mul, eval_C, eval_X, positiveMinor, pow_succ]
  ring

/--
The stated quantitative bound `0 < J.positiveMinor n`.

Use: `chebyshev2.Jacobi.choleskyDiagonal_pos` uses this bound to establish the stated
quantitative bound `0 < J.choleskyDiagonal i`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Use the identities/estimates `chebyshev2.Jacobi.positiveMinor_eq_det`,
`chebyshev1.JacobiData.matrix_principal_block` with the arguments shown in the proof.
-/
theorem positiveMinor_pos (h : (1+J.matrix).PosDef) (n : ℕ) (hn : n ≤ N) :
    0 < J.positiveMinor n := by
  -- Use the identities/estimates `chebyshev2.Jacobi.positiveMinor_eq_det`,
  -- `chebyshev1.JacobiData.matrix_principal_block` with the arguments shown in the proof.
  rw [J.positiveMinor_eq_det]
  let e : Fin n → Fin N := fun i => ⟨i.val,by omega⟩
  have hi : Function.Injective e := by
    intro i j he
    apply Fin.ext
    simpa [e] using congrArg Fin.val he
  have hp := h.submatrix hi
  have he : (1+J.matrix).submatrix e e = 1+J.data.matrix 0 n := by
    simp only [Matrix.submatrix_add, Pi.add_apply]
    rw [Matrix.submatrix_one e hi]
    change 1+(J.data.matrix 0 N).submatrix e e = _
    have hh : (J.data.matrix 0 N).submatrix e e = J.data.matrix 0 n := by
      simpa only [Nat.zero_add] using J.data.matrix_principal_block N 0 n (by omega)
    rw [hh]
  rw [he] at hp
  exact hp.det_pos

/--
Defines `choleskyDiagonal` of type `ℝ` by `sqrt (J.positiveMinor (i.val+1)/(2*J.positiveMinor
i.val))`.

Use: `chebyshev2.Jacobi.cholesky` uses this definition in the displayed construction of
`cholesky`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.
-/
def choleskyDiagonal (i : Fin N) : ℝ := sqrt (J.positiveMinor (i.val+1)/(2*J.positiveMinor i.val))
/--
Defines `choleskyLower` of type `ℝ` by `sqrt (J.data.aSq i.val*J.positiveMinor
(i.val-1)/(2*J.positiveMinor i.val))`.

Use: `chebyshev2.Jacobi.cholesky` uses this definition in the displayed construction of
`cholesky`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.
-/
def choleskyLower (i : Fin N) : ℝ :=
  sqrt (J.data.aSq i.val*J.positiveMinor (i.val-1)/(2*J.positiveMinor i.val))
/--
Defines `cholesky` of type `` by `Bidiagonal.matrix J.choleskyDiagonal J.choleskyLower`.

Use: `chebyshev2.Jacobi.cholesky_factor` rewrites with this definition to establish exact
identity `J.cholesky*J.choleskyᵀ = (1/2:ℝ) • (1+J.matrix)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.
-/
def cholesky := Bidiagonal.matrix J.choleskyDiagonal J.choleskyLower

/--
The stated quantitative bound `0 < J.choleskyDiagonal i`.

Use: `chebyshev2.Jacobi.cholesky_offdiagonal_identity` uses this bound to establish exact
identity `J.choleskyDiagonal i*J.choleskyLower j = sqrt (J.data.aSq j.val)/2`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_unique`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Use the identities/estimates `chebyshev2.Jacobi.positiveMinor_pos` with the
arguments shown in the proof.
-/
theorem choleskyDiagonal_pos (h : (1+J.matrix).PosDef) (i : Fin N) :
    0 < J.choleskyDiagonal i := sqrt_pos.mpr
  (div_pos (J.positiveMinor_pos h (i.val+1) (by omega))
    (mul_pos (by norm_num) (J.positiveMinor_pos h i.val (by omega))))

/--
Exact identity `J.choleskyLower i = 0`.

Use: `chebyshev2.Jacobi.cholesky_unique` uses this identity to establish the identity `d
= J.choleskyDiagonal ∧ l = J.choleskyLower`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_unique`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem choleskyLower_zero (i : Fin N) (hi : i.val = 0) : J.choleskyLower i = 0 := by simp [choleskyLower, hi, J.coupling_zero]

/--
The stated quantitative bound `0 < J.choleskyLower i`.

Use: `chebyshev2.Jacobi.lift_centered` uses this bound to establish the precise assertion
is `J.lift.Centered`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.lift_centered`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Use the identities/estimates `chebyshev2.Jacobi.positiveMinor_pos` with the
arguments shown in the proof.
-/
theorem choleskyLower_pos (h : (1+J.matrix).PosDef) (hir : J.Irreducible)
    (i : Fin N) (hi : 0 < i.val) : 0 < J.choleskyLower i := sqrt_pos.mpr
  (div_pos (mul_pos (hir i.val hi i.isLt) (J.positiveMinor_pos h (i.val-1) (by omega)))
    (mul_pos (by norm_num) (J.positiveMinor_pos h i.val (by omega))))

/--
Exact identity `J.choleskyDiagonal i^2 = J.positiveMinor (i.val+1)/(2*J.positiveMinor i.val)`.

Use: `chebyshev2.Jacobi.cholesky_diagonal_identity` rewrites with this identity to
establish exact identity `J.choleskyDiagonal i^2 + (if 0 < i.val then J.choleskyLower i^2 else
0) = (1+J.data.b i.val)/2`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Use the identities/estimates `chebyshev2.Jacobi.positiveMinor_pos` with the
arguments shown in the proof.
-/
theorem choleskyDiagonal_sq (h : (1+J.matrix).PosDef) (i : Fin N) :
    J.choleskyDiagonal i^2 = J.positiveMinor (i.val+1)/(2*J.positiveMinor i.val) :=
  sq_sqrt (div_pos (J.positiveMinor_pos h (i.val+1) (by omega))
    (mul_pos (by norm_num) (J.positiveMinor_pos h i.val (by omega)))).le

/--
Exact identity `J.choleskyLower i^2 = J.data.aSq i.val*J.positiveMinor
(i.val-1)/(2*J.positiveMinor i.val)`.

Use: `chebyshev2.Jacobi.cholesky_diagonal_identity` rewrites with this identity to
establish exact identity `J.choleskyDiagonal i^2 + (if 0 < i.val then J.choleskyLower i^2 else
0) = (1+J.data.b i.val)/2`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Use the identities/estimates `chebyshev2.Jacobi.positiveMinor_pos` with the
arguments shown in the proof.
-/
theorem choleskyLower_sq (h : (1+J.matrix).PosDef) (i : Fin N) :
    J.choleskyLower i^2 =
      J.data.aSq i.val*J.positiveMinor (i.val-1)/(2*J.positiveMinor i.val) :=
  sq_sqrt (div_nonneg (mul_nonneg (J.coupling_nonneg i.val)
    (J.positiveMinor_pos h (i.val-1) (by omega)).le)
    (mul_pos (by norm_num) (J.positiveMinor_pos h i.val (by omega))).le)

/--
Exact identity `J.choleskyDiagonal i^2 + (if 0 < i.val then J.choleskyLower i^2 else 0) =
(1+J.data.b i.val)/2`.

Use: `chebyshev2.Jacobi.cholesky_factor` uses this identity to establish the identity
`J.cholesky*J.choleskyᵀ = (1/2:ℝ) • (1+J.matrix)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Separate `0 < i.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem cholesky_diagonal_identity (h : (1+J.matrix).PosDef) (i : Fin N) :
    J.choleskyDiagonal i^2 + (if 0 < i.val then J.choleskyLower i^2 else 0) =
      (1+J.data.b i.val)/2 := by
  -- Separate `0 < i.val` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  rw [J.choleskyDiagonal_sq h i]
  by_cases hi : 0 < i.val
  · rw [ite_eq_left hi, J.choleskyLower_sq h i]
    have hr := J.positiveMinor_recurrence (i.val-1)
    rw [show i.val-1+2 = i.val+1 by omega, show i.val-1+1 = i.val by omega] at hr
    rw [hr]
    field_simp [(J.positiveMinor_pos h i.val (by omega)).ne']
    ring
  · have hi0 : i.val = 0 := by omega
    simp [hi0, J.positiveMinor_one]

/--
Exact identity `J.choleskyDiagonal i*J.choleskyLower j = sqrt (J.data.aSq j.val)/2`.

Use: `chebyshev2.Jacobi.cholesky_factor` rewrites with this identity to establish exact
identity `J.cholesky*J.choleskyᵀ = (1/2:ℝ) • (1+J.matrix)`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cholesky_offdiagonal_identity (h : (1+J.matrix).PosDef) (i j : Fin N)
    (hij : i.val+1 = j.val) : J.choleskyDiagonal i*J.choleskyLower j = sqrt (J.data.aSq j.val)/2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd := J.choleskyDiagonal_sq h i
  have hl := J.choleskyLower_sq h j
  have hj : j.val-1 = i.val := by omega
  rw [hj, ← hij] at hl
  have he : (J.choleskyDiagonal i*J.choleskyLower j)^2 = J.data.aSq j.val/4 := by
    rw [mul_pow, hd, hl]
    rw [← hij]
    field_simp [(J.positiveMinor_pos h i.val (by omega)).ne',
      (J.positiveMinor_pos h (i.val+1) (by omega)).ne']
    ring
  have hs := sq_sqrt (J.coupling_nonneg j.val)
  have hp : 0 ≤ J.choleskyDiagonal i*J.choleskyLower j :=
    mul_nonneg (J.choleskyDiagonal_pos h i).le (sqrt_nonneg _)
  have hq := sqrt_nonneg (J.data.aSq j.val)
  nlinarith

/--
The bidiagonal Cholesky factor in Theorem A.1, constructed from actual minors.

Exact identity `J.cholesky*J.choleskyᵀ = (1/2:ℝ) • (1+J.matrix)`.

Use: `chebyshev2.Jacobi.cholesky_unique` uses this identity to establish the identity `d
= J.choleskyDiagonal ∧ l = J.choleskyLower`.

Article: chebyshev2, Theorem A.1.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Separate `i = j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem cholesky_factor (h : (1+J.matrix).PosDef) : J.cholesky*J.choleskyᵀ = (1/2:ℝ) • (1+J.matrix) := by
  -- Separate `i = j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  ext i j
  rw [cholesky, Bidiagonal.mul_transpose_apply]
  simp only [Matrix.smul_apply, Matrix.add_apply, matrix, J.data.matrix_apply, Nat.zero_add,
    smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simpa [div_eq_mul_inv, mul_comm] using J.cholesky_diagonal_identity h i
  · simp only [hij, ite_false]
    by_cases ha : i.val+1 = j.val
    · simp only [ha, ite_true]
      rw [J.cholesky_offdiagonal_identity h i j ha]; ring
    · simp only [ha, ite_false]
      by_cases hb : j.val+1 = i.val
      · simp only [hb, ite_true]
        rw [mul_comm, J.cholesky_offdiagonal_identity h j i hb]; ring
      · simp [hb]

/--
Uniqueness of the factor, including its finite coefficient representation.

Exact identity `d = J.choleskyDiagonal ∧ l = J.choleskyLower`.

Use: `chebyshev2.Centering.extractedBlock_is_cholesky` uses this identity to establish
exact identity `extractedBlock C = (compression C).cholesky`.

Article: chebyshev2, Theorem A.1.

Source: Meurant, A review on the inverse of symmetric tridiagonal and block tridiagonal
matrices — tridiagonal inverse factorization.

Proof: Use the identities/estimates `chebyshev2.Bidiagonal.factor_unique`,
`chebyshev2.Jacobi.choleskyDiagonal_pos`, `chebyshev2.Jacobi.choleskyLower_zero` with
the arguments shown in the proof.
-/
theorem cholesky_unique (h : (1+J.matrix).PosDef) (d l : Fin N → ℝ)
    (hd : ∀ i, 0 < d i) (hl : ∀ i, i.val = 0 → l i = 0)
    (hf : Bidiagonal.matrix d l * (Bidiagonal.matrix d l)ᵀ = (1/2:ℝ) • (1+J.matrix)) :
    d = J.choleskyDiagonal ∧ l = J.choleskyLower :=
  Bidiagonal.factor_unique d l J.choleskyDiagonal J.choleskyLower hd
    (J.choleskyDiagonal_pos h) hl J.choleskyLower_zero
    (hf.trans (J.cholesky_factor h).symm)

end
end chebyshev2.Jacobi
