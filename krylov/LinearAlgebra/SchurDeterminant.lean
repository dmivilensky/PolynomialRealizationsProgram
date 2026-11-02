import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine Schur determinant and inverse blocks.
Use: identify true partially shifted block determinants with the actual normalized Schur polynomial, and derive genuine positivity and the real principal inverse block.
Source: standard Schur-complement block factorization, mathlib Matrix.det_fromBlocks and actual nonsingular inverse identities; positive principal submatrices reuse the genuine positive-definite matrix inverse.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A genuine nonsingular leading block gives the actual Schur-complement determinant factorization.
Use: A genuine nonsingular leading block gives the actual Schur-complement determinant factorization.
Article: main_krylov, prop:phi(a), genuine Schur determinant and inverse blocks.
Proof: Use the standard true block determinant theorem with its real determinant-derived inverse domain. -/
theorem block_schur_det (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D).det=A.det*(D-C*A⁻¹*B).det := by
  let : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  simpa only [Matrix.invOf_eq_nonsing_inv] using Matrix.det_fromBlocks₁₁ A B C D

/-- The actual shifted determinant divided by the true positive-model determinant equals the genuine inverse-normalized determinant.
Use: The actual shifted determinant divided by the true positive-model determinant equals the genuine inverse-normalized determinant.
Article: main_krylov, prop:phi(a), genuine Schur determinant and inverse blocks.
Proof: Factor the real shifted matrix by its actual nonsingular model and cancel its genuine determinant. -/
theorem schur_normalized_shift (S : Matrix n n ℝ) (hS : IsUnit S.det) (lam : ℝ) :
    (S-lam • 1).det/S.det=(1-lam • S⁻¹).det := by
  have he : S-lam • 1=(1-lam • S⁻¹)*S := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.nonsing_inv_mul _ hS]
  rw [he,Matrix.det_mul]
  exact mul_div_cancel_right₀ _ (isUnit_iff_ne_zero.mp hS)

/-- Shifting only the actual trailing diagonal block gives exactly the genuine inverse-normalized Schur determinant.
Use: Shifting only the actual trailing diagonal block gives exactly the genuine inverse-normalized Schur determinant.
Article: main_krylov, prop:phi(a), genuine Schur determinant and inverse blocks.
Proof: Apply actual block factorization to both true pencils, cancel the real leading determinant and use the genuine Schur normalization. -/
theorem block_schur_shift_ratio (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (hA : IsUnit A.det) (hS : IsUnit (D-C*A⁻¹*B).det) (lam : ℝ) :
    (Matrix.fromBlocks A B C (D-lam • 1)).det/(Matrix.fromBlocks A B C D).det=
      (1-lam • (D-C*A⁻¹*B)⁻¹).det := by
  rw [block_schur_det A B C _ hA,block_schur_det A B C D hA]
  have he : D-lam • 1-C*A⁻¹*B=(D-C*A⁻¹*B)-lam • 1 := by abel
  rw [he,mul_div_mul_left _ _ (isUnit_iff_ne_zero.mp hA),schur_normalized_shift _ hS lam]

/-- The actual trailing principal block of a genuine nonsingular block inverse is precisely the true Schur inverse.
Use: The actual trailing principal block of a genuine nonsingular block inverse is precisely the true Schur inverse.
Article: main_krylov, prop:phi(a), genuine Schur determinant and inverse blocks.
Proof: Use the standard real inverse-block formula on its actual leading, Schur and whole-matrix determinant domains. -/
theorem block_schur_inverse (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (hA : IsUnit A.det) (hS : IsUnit (D-C*A⁻¹*B).det) (hT : IsUnit (Matrix.fromBlocks A B C D).det) :
    ((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inr Sum.inr=(D-C*A⁻¹*B)⁻¹ := by
  -- All genuine inverse-block typeclass domains come from the actual three determinant hypotheses.
  let : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  have hS' : IsUnit (D-C*⅟A*B).det := by simpa only [Matrix.invOf_eq_nonsing_inv] using hS
  let : Invertible (D-C*⅟A*B) := Matrix.invertibleOfIsUnitDet _ hS'
  let : Invertible (Matrix.fromBlocks A B C D) := Matrix.invertibleOfIsUnitDet _ hT
  have he := Matrix.invOf_fromBlocks₁₁_eq A B C D
  simp only [Matrix.invOf_eq_nonsing_inv] at he
  rw [he]
  rfl

/-- The genuine Schur complement of an actual positive block matrix is truly positive definite.
Use: The genuine Schur complement of an actual positive block matrix is truly positive definite.
Article: main_krylov, prop:phi(a), genuine Schur determinant and inverse blocks.
Proof: Derive its real nonsingular determinant from actual block factorization; its true inverse is a positive principal block of the genuine positive whole inverse. Invert that actual positive block back to the real Schur complement. -/
theorem block_schur_posDef (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (hT : (Matrix.fromBlocks A B C D).PosDef) : (D-C*A⁻¹*B).PosDef := by
  -- The true leading principal block is positive and the actual determinant factorization proves genuine Schur nonsingularity.
  have hA : A.PosDef := by
    exact hT.submatrix (Sum.inl_injective : Function.Injective (Sum.inl : m → m ⊕ n))
  have hAd := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hTd := isUnit_iff_ne_zero.mpr hT.det_pos.ne'
  have hS : IsUnit (D-C*A⁻¹*B).det := by
    apply isUnit_iff_ne_zero.mpr
    have hh := hT.det_pos.ne'
    rw [block_schur_det A B C D hAd] at hh
    exact (mul_ne_zero_iff.mp hh).2
  -- The actual Schur inverse is a genuinely positive principal block of the true whole inverse.
  have hp := hT.inv.submatrix (Sum.inr_injective : Function.Injective (Sum.inr : n → m ⊕ n))
  rw [block_schur_inverse A B C D hAd hS hTd] at hp
  have hi := hp.inv
  rw [Matrix.nonsing_inv_nonsing_inv _ hS] at hi
  exact hi
end
end krylov.LinearAlgebra
