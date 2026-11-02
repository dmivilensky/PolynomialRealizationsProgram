import krylov.Completion.StrictJacobiBand
import krylov.LinearAlgebra.SchurDeterminant
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), actual endpoint kernels.
Use: construct a nonzero actual endpoint null vector by the original scalar
Schur determinant, without assuming a spectral node of an endpoint matrix.
Source: standard block determinant and determinant/kernel equivalence, with
all genuine leading inverse domains derived from positive definiteness.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {p : ℕ}
/-- The actual scalar-corner determinant is the true leading determinant times
its literal scalar Schur pivot.
Use: endpoint completions have the prescribed spectral node without an assumed
whole-matrix nonsingularity or an abstract quadrature existence witness.
Article: main_krylov, s5:fibre(b).
Proof: the proved positive leading domain provides its actual inverse, and the
standard block determinant reduces the true singleton remainder to its entry. -/
theorem strict_scalar_schur_det (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.PosDef)
    (x : Fin p → ℝ) (c : ℝ) :
    (fromBlocks (scalarCorner c) (crossColumn x)ᵀ (crossColumn x) H).det=
      H.det*(c-x ⬝ᵥ (H⁻¹*ᵥ x)) := by
  let : Invertible H := Matrix.invertibleOfIsUnitDet H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
  rw [Matrix.det_fromBlocks₂₂,Matrix.invOf_eq_nonsing_inv,crossColumn_quadratic,Matrix.det_fin_one]
  rfl

/-- The actual zero-Schur-pivot completion has a nonzero genuine null vector.
Use: the prescribed endpoint node is derived for the real completed matrix.
Article: main_krylov, s5:fibre(b).
Proof: its computed real determinant vanishes, so the actual finite linear map
has a nonzero kernel vector by the standard matrix determinant criterion. -/
theorem strict_scalar_schur_kernel (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.PosDef)
    (x : Fin p → ℝ) :
    ∃ v : Fin 1⊕Fin p → ℝ,v≠0 ∧
      fromBlocks (scalarCorner (x ⬝ᵥ (H⁻¹*ᵥ x))) (crossColumn x)ᵀ (crossColumn x) H*ᵥ v=0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mpr
  rw [strict_scalar_schur_det H hH x,sub_self,mul_zero]

end
end krylov.Completion
