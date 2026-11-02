import krylov.Strings.DiscreteIdentification
import krylov.LinearAlgebra.StrictSpectralShifts
import krylov.LinearAlgebra.LeadingPosDef

/-!
Article: `main_krylov`, `apC:prop:local` and `apC:lem:topimp`.
The top solution is evaluated from the actual physical position and flux
polynomials. Strict positivity follows from the genuine shifted path form
and its leading principal determinants, rather than from a supplied sign
certificate. The resulting impedances are the source's physical quantities.
Source: Sylvester's criterion and the already verified finite Jacobi
continuant determinant identity.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- Actual alternating position polynomial at the upper spectral parameter. -/
def topA (Λ : ℝ) (k : ℕ) : ℝ := (-1 : ℝ)^k * (S.φPolynomial k).eval Λ

/-- Actual alternating flux polynomial at the upper spectral parameter. -/
def topB (Λ : ℝ) (k : ℕ) : ℝ := (-1 : ℝ)^(k+1) * (S.pPolynomial k).eval Λ

@[simp] theorem topA_zero (Λ : ℝ) : S.topA Λ 0 = 1 := by simp [topA]
@[simp] theorem topB_zero (Λ : ℝ) : S.topB Λ 0 = Λ := by simp [topB]

/-- Literal drift recurrence for the evaluated physical top solution. -/
theorem topA_succ (Λ : ℝ) (k : ℕ) :
    S.topA Λ (k+1) = S.gap k * S.topB Λ k - S.topA Λ k := by
  simp only [topA, topB, S.φPolynomial_succ, eval_add, eval_mul, eval_C, pow_succ]
  ring

/-- Literal mass recurrence for the evaluated physical top flux. -/
theorem topB_succ (Λ : ℝ) (k : ℕ) :
    S.topB Λ (k+1) = Λ*S.mass (k+1)*S.topA Λ (k+1) - S.topB Λ k := by
  simp only [topB, topA, S.pPolynomial_succ, eval_sub, eval_mul, eval_X, eval_C,
    pow_succ]
  ring

/-- The genuine normalized path form is strictly below every strict norm
upper bound, in the positive-edge orientation used for its continuants. -/
theorem top_shift_posDef {Λ : ℝ} (hΛ : S.spectralRadius < Λ) :
    (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) - S.jacobi.matrix).PosDef := by
  have hA : (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) - S.operator).PosDef :=
    (krylov.LinearAlgebra.positive_upper_shift_iff _ S.operator_isHermitian Λ).mpr
      (fun i ↦ (S.operator_eigenvalue_le i).trans_lt hΛ)
  have hinj : Function.Injective S.signMatrix.mulVec := by
    intro x y h
    have hh := congrArg (fun z ↦ S.signMatrix *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, S.signMatrix_sq, Matrix.one_mulVec] using hh
  have hp := hA.conjTranspose_mul_mul_same (B := S.signMatrix) hinj
  have he : S.signMatrixᴴ * (Λ • 1 - S.operator) * S.signMatrix =
      Λ • 1 - S.jacobi.matrix := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, S.signMatrix_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      S.signMatrix_sq, S.jacobi_matrix]
    rfl
  rwa [he] at hp

/-- Every true leading physical Jacobi determinant is positive above the
actual spectral norm, including the whole terminal determinant. -/
theorem top_leading_pos {Λ : ℝ} (hΛ : S.spectralRadius < Λ) {k : ℕ} (hk : k≤N+1) :
    0 < (S.jacobi.data.leading k).eval Λ := by
  let e : Fin k → Fin (N+1) := fun i ↦ ⟨0+i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Fin.ext
    simpa only [e, Nat.zero_add] using congrArg Fin.val h
  have hsub : (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) - S.jacobi.matrix).submatrix e e =
      Λ • 1 - S.jacobi.data.matrix 0 k := by
    change (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)).submatrix e e -
      (S.jacobi.data.matrix 0 (N+1)).submatrix e e = _
    rw [S.jacobi.data.matrix_principal_block (N+1) 0 k (by omega)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      he.eq_iff]
  have hd := ((S.top_shift_posDef hΛ).submatrix he).det_pos
  rw [hsub] at hd
  rw [JacobiData.leading, S.jacobi.data.block_eq_charpoly S.jacobi.coupling_nonneg,
    Matrix.eval_charpoly]
  convert hd using 1
  congr 2
  ext i j
  by_cases hij : i=j <;> simp [Matrix.scalar, hij]

/-- Every actual top position is strictly positive above the actual path
norm; the sign follows from its true leading principal determinant. -/
theorem topA_pos {Λ : ℝ} (hΛ : S.spectralRadius < Λ) (k : ℕ) (hk : k≤N) :
    0 < S.topA Λ k := by
  let i : Fin (N+1) := ⟨k, by omega⟩
  have hnorm : normalizedLeading S.jacobi k = S.spectralData.orthogonalPolynomial i := by
    rw [← S.spectralData_reconstructed]
    exact normalizedLeading_eq_orthogonalPolynomial S.spectralData i
  have hid := congrArg (fun P : ℝ[X] ↦ P.eval Λ) (S.orthogonalPolynomial_eq i)
  have he : (normalizedLeading S.jacobi k).eval Λ =
      Real.sqrt (S.mass k) * S.topA Λ k := by
    rw [hnorm, hid]
    simp only [eval_mul, eval_C, topA]
    ring
  have hp : 0 < (normalizedLeading S.jacobi k).eval Λ := by
    simp only [normalizedLeading, eval_mul, eval_C]
    exact mul_pos (inv_pos.mpr (linkProduct_pos S.jacobi_irreducible i.isLt))
      (S.top_leading_pos hΛ (by omega))
  rw [he] at hp
  exact pos_of_mul_pos_right hp (Real.sqrt_nonneg _)

/-- Every used actual top flux is positive; both adjacent top positions
are positive and their sum is the genuine gap times that flux. -/
theorem topB_pos {Λ : ℝ} (hΛ : S.spectralRadius < Λ) (k : ℕ) (hk : k<N) :
    0 < S.topB Λ k := by
  have ha := S.topA_pos hΛ k (by omega)
  have hb := S.topA_pos hΛ (k+1) (by omega)
  have he := S.topA_succ Λ k
  have hg := S.gap_pos k hk
  nlinarith

/-- The upper outgoing impedance of an actual edge. -/
def topC (Λ : ℝ) (k : ℕ) : ℝ := S.topB Λ k / (Real.sqrt Λ * S.topA Λ k)

/-- The upper incoming impedance at a positive site. -/
def topC' (Λ : ℝ) (k : ℕ) : ℝ := S.topB Λ (k-1) / (Real.sqrt Λ * S.topA Λ k)

/-- Every physical outgoing top impedance is positive. -/
theorem topC_pos {Λ : ℝ} (hΛ : S.spectralRadius < Λ) (k : ℕ) (hk : k<N) :
    0 < S.topC Λ k := by
  have hΛ0 : 0<Λ := (norm_nonneg S.operator).trans_lt hΛ
  exact div_pos (S.topB_pos hΛ k hk)
    (mul_pos (Real.sqrt_pos.mpr hΛ0) (S.topA_pos hΛ k (by omega)))

/-- Every physical incoming top impedance is positive. -/
theorem topC'_pos {Λ : ℝ} (hΛ : S.spectralRadius < Λ) (k : ℕ)
    (hk0 : 0<k) (hk : k≤N) : 0 < S.topC' Λ k := by
  have hΛ0 : 0<Λ := (norm_nonneg S.operator).trans_lt hΛ
  exact div_pos (S.topB_pos hΛ (k-1) (by omega))
    (mul_pos (Real.sqrt_pos.mpr hΛ0) (S.topA_pos hΛ k hk))

/-- Exact bond pairing identity for the actual upper impedances. -/
theorem top_bond_identity {Λ : ℝ} (hΛ : S.spectralRadius < Λ) (k : ℕ) (hk : k<N) :
    Real.sqrt Λ * S.gap k = (S.topC Λ k)⁻¹ + (S.topC' Λ (k+1))⁻¹ := by
  have hΛ0 : 0<Λ := (norm_nonneg S.operator).trans_lt hΛ
  have hs := (Real.sqrt_pos.mpr hΛ0).ne'
  have ha := (S.topA_pos hΛ k (by omega)).ne'
  have hb := (S.topA_pos hΛ (k+1) (by omega)).ne'
  have hc := (S.topB_pos hΛ k hk).ne'
  have he := S.topA_succ Λ k
  simp only [topC, topC', Nat.add_sub_cancel, inv_div]
  field_simp
  nlinarith [he]

/-- Exact interior mass pairing identity for the actual upper impedances. -/
theorem top_mass_identity {Λ : ℝ} (hΛ : S.spectralRadius < Λ) (k : ℕ)
    (hk0 : 0<k) (hk : k<N) :
    Real.sqrt Λ * S.mass k = S.topC Λ k + S.topC' Λ k := by
  have hΛ0 : 0<Λ := (norm_nonneg S.operator).trans_lt hΛ
  have hs := (Real.sqrt_pos.mpr hΛ0).ne'
  have ha := (S.topA_pos hΛ k (by omega)).ne'
  have he := S.topB_succ Λ (k-1)
  rw [Nat.sub_add_cancel (by omega)] at he
  simp only [topC, topC']
  field_simp
  rw [Real.sq_sqrt hΛ0.le]
  linarith

end
end krylov.Strings.DiscreteString
