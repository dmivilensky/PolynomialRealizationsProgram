import krylov.LinearAlgebra.SchurDeterminant
import Mathlib.Analysis.Matrix.PosDef
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine finite Schur spectral product.
Use: evaluate the actual inverse-normalized positive matrix pencil using the true positive eigenvalues of that same matrix.
Source: mathlib finite real spectral theorem and actual characteristic-polynomial determinant identity.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Polynomial
open scoped BigOperators
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual shifted Hermitian determinant is the product of its genuine eigenvalue shifts.
Use: The actual shifted Hermitian determinant is the product of its genuine eigenvalue shifts.
Article: main_krylov, prop:phi(a), genuine finite Schur spectral product.
Proof: Use the true characteristic polynomial and track the actual determinant sign through all finite factors. -/
theorem hermitian_shift_det (S : Matrix n n ℝ) (hS : S.IsHermitian) (lam : ℝ) :
    (S-lam • 1).det=∏ i,(hS.eigenvalues i-lam) := by
  -- The actual characteristic-polynomial sign cancels exactly once for each true finite spectral factor.
  have he : S-lam • 1= -(lam • 1-S) := by module
  rw [he,Matrix.det_neg]
  have heval : (lam • (1 : Matrix n n ℝ)-S).det=S.charpoly.eval lam := by
    rw [Matrix.eval_charpoly]
    rw [Matrix.smul_one_eq_diagonal,Matrix.scalar_apply]
  rw [heval]
  rw [hS.charpoly_eq,Polynomial.eval_prod]
  simp only [eval_sub,eval_X,eval_C,RCLike.ofReal_real_eq_id,id_eq]
  rw [show (-1:ℝ)^Fintype.card n=∏ _i : n,(-1:ℝ) by simp,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- The true inverse-normalized positive pencil is the product of its genuine positive spectral factors.
Use: The true inverse-normalized positive pencil is the product of its genuine positive spectral factors.
Article: main_krylov, prop:phi(a), genuine finite Schur spectral product.
Proof: Divide the actual shifted determinant by the true eigenvalue determinant product; positivity supplies every actual nonzero divisor. -/
theorem positive_normalized_shift_product (S : Matrix n n ℝ) (hS : S.PosDef) (lam : ℝ) :
    (1-lam • S⁻¹).det=∏ i,(1-lam/hS.1.eigenvalues i) := by
  rw [← schur_normalized_shift S (isUnit_iff_ne_zero.mpr hS.det_pos.ne') lam,
    hermitian_shift_det S hS.1 lam,hS.1.det_eq_prod_eigenvalues,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  dsimp
  field_simp [(hS.eigenvalues_pos i).ne']
end
end krylov.LinearAlgebra
