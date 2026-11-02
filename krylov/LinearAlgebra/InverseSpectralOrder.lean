import krylov.LinearAlgebra.SpectralConditioning
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual inverse spectral interval tests.
Use: express true shifted positivity of the actual positive matrix inverse in its genuine original spectral coordinates.
Source: reuse the proved spectral inverse, orthogonal positivity equivalence and actual positive eigenvalue domains.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
variable {n : ℕ}

/-- The actual positive matrix inverse has the genuine reciprocal diagonal in its original spectral basis.
Use: The actual positive matrix inverse has the genuine reciprocal diagonal in its original spectral basis.
Article: main_krylov, prop:phi(a), actual inverse spectral interval tests.
Proof: Identify the true nonsingular inverse with the proved actual spectral inverse. -/
theorem positive_inverse_coordinates (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosDef) :
    (SpectralBasis.ofHermitian T hT.1).coordinates T⁻¹=
      Matrix.diagonal (fun i => (hT.1.eigenvalues i)⁻¹) := by
  rw [← pseudoinverse_eq_inv T hT.1 (isUnit_iff_ne_zero.mpr hT.det_pos.ne')]
  exact coordinates_pseudoinverse _

/-- A genuine lower shifted inverse positivity test is exactly the corresponding true reciprocal eigenvalue lower bounds.
Use: A genuine lower shifted inverse positivity test is exactly the corresponding true reciprocal eigenvalue lower bounds.
Article: main_krylov, prop:phi(a), actual inverse spectral interval tests.
Proof: Use actual orthogonal positivity invariance and the genuine reciprocal inverse diagonal. -/
theorem inverse_lower_shift_iff (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosDef) (c : ℝ) :
    (T⁻¹-c • 1).PosSemidef ↔ ∀ i,c≤(hT.1.eigenvalues i)⁻¹ := by
  -- Work in the original matrix eigenbasis so reciprocal eigenvalues keep their true labels.
  let B := SpectralBasis.ofHermitian T hT.1
  rw [← coordinates_posSemidef_iff B]
  have he : B.coordinates (T⁻¹-c • 1)=Matrix.diagonal (fun i => (hT.1.eigenvalues i)⁻¹-c) := by
    change B.Qᵀ*(T⁻¹-c • 1)*B.Q=_
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,B.transpose_mul]
    change B.coordinates T⁻¹-c • 1=_
    rw [positive_inverse_coordinates T hT]
    ext i j
    by_cases hij : i=j <;> simp [hij]
  rw [he,Matrix.posSemidef_diagonal_iff]
  simp only [sub_nonneg]

/-- A genuine upper shifted inverse positivity test is exactly the corresponding true reciprocal eigenvalue upper bounds.
Use: A genuine upper shifted inverse positivity test is exactly the corresponding true reciprocal eigenvalue upper bounds.
Article: main_krylov, prop:phi(a), actual inverse spectral interval tests.
Proof: Use actual orthogonal positivity invariance and the genuine reciprocal inverse diagonal. -/
theorem inverse_upper_shift_iff (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosDef) (c : ℝ) :
    (c • 1-T⁻¹).PosSemidef ↔ ∀ i,(hT.1.eigenvalues i)⁻¹≤c := by
  -- Diagonalize the actual inverse in the original eigenbasis before testing the genuine upper shift.
  let B := SpectralBasis.ofHermitian T hT.1
  rw [← coordinates_posSemidef_iff B]
  have he : B.coordinates (c • 1-T⁻¹)=Matrix.diagonal (fun i => c-(hT.1.eigenvalues i)⁻¹) := by
    change B.Qᵀ*(c • 1-T⁻¹)*B.Q=_
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,B.transpose_mul]
    change c • 1-B.coordinates T⁻¹=_
    rw [positive_inverse_coordinates T hT]
    ext i j
    by_cases hij : i=j <;> simp [hij]
  rw [he,Matrix.posSemidef_diagonal_iff]
  simp only [sub_nonneg]
end
end krylov.LinearAlgebra
