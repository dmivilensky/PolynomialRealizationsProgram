import krylov.Design.MomentMinimum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: main_krylov, thm:B, differentiation of c-information.
Use: differentiate the actual inverse-matrix information along an affine
moment perturbation, with the normalized inverse column as its gradient.
Source: the inverse derivative -G^-1 D G^-1, imported from mathlib's Banach
algebra calculus, and the standard c-information chain rule.
-/

namespace krylov.Design
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A symmetric matrix sandwich diagonal is the corresponding inverse-column quadratic form.
Article: main_krylov, thm:B. -/
theorem sandwich_diagonal (B D : Matrix n n ℝ) (hB : B.IsSymm) (i : n) :
    (B * D * B) i i = (B *ᵥ Pi.single i 1) ⬝ᵥ (D *ᵥ (B *ᵥ Pi.single i 1)) := by
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hs : B i j = B j i := (hB.apply i j).symm
  rw [hs]
  ring

/-- Differentiate the actual matrix inverse along an affine perturbation.
Article: main_krylov, thm:B.
Proof: apply mathlib's general Banach-algebra inverse derivative at the unit represented by G. -/
theorem matrix_inverse_affine_hasDerivAt (G D : Matrix n n ℝ) (hG : IsUnit G) :
    HasDerivAt (fun s : ℝ => (G + s • D)⁻¹) (-(G⁻¹ * D * G⁻¹)) 0 := by
  obtain ⟨u, hu⟩ := hG
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hp : HasDerivAt (fun s : ℝ => G + s • D) D 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add G using 1
    simp
  have hbase : G + (0 : ℝ) • D = (u : Matrix n n ℝ) := by simpa using hu.symm
  rw [← hbase] at hi
  have hd := hi.comp_hasDerivAt 0 hp
  have huinv : (↑u⁻¹ : Matrix n n ℝ) = G⁻¹ := by
    rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, zero_smul, add_zero,
    huinv] using! hd

/-- The scalar inverse-diagonal c-information has exactly the minimizing-column quadratic derivative.
Article: main_krylov, thm:B, the finite-matrix directional derivative.
Proof: compose the matrix inverse derivative, the continuous entry functional,
and the real reciprocal; then identify the inverse sandwich with the minimizing column. -/
theorem inverseInformation_hasDerivAt (G D : Matrix n n ℝ) (hG : G.PosDef) (i : n) :
    HasDerivAt (fun s : ℝ => (((G + s • D)⁻¹) i i)⁻¹)
      (normalizedInverseColumn G i ⬝ᵥ (D *ᵥ normalizedInverseColumn G i)) 0 := by
  let L : Matrix n n ℝ →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i i).toContinuousLinearMap
  have he := L.hasFDerivAt.comp_hasDerivAt 0 (matrix_inverse_affine_hasDerivAt G D hG.isUnit)
  have hentry : HasDerivAt (fun s : ℝ => ((G + s • D)⁻¹) i i)
      (-(G⁻¹ * D * G⁻¹) i i) 0 := by
    convert! he using 1
  have hk : 0 < G⁻¹ i i := hG.inv.diag_pos
  have hi := hentry.inv (by simpa using hk.ne')
  convert! hi using 1
  simp only [normalizedInverseColumn, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, zero_smul, add_zero]
  rw [← sandwich_diagonal G⁻¹ D (Matrix.isHermitian_iff_isSymm.mp hG.inv.isHermitian) i]
  ring

end
end krylov.Design
