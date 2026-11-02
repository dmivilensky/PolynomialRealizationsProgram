import krylov.LinearAlgebra.PositiveCauchy
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), strict Schur inverse comparison.
Use: obtain strict spectral information-fibre endpoint gaps from actual positive
leading forms and a genuine nonzero irreducible Jacobi coupling column.
Source: the classical variational inverse quadratic form, proved directly by
expanding one actual positive completed square; no inverse-order theorem is assumed.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
variable {p : ℕ}

/-- A genuine positive downward scalar shift strictly increases the inverse
quadratic form on every actual nonzero vector.
Use: the lower spectral fibre pivot lies strictly above mu plus its true
positive-Jacobi Schur correction.
Article: main_krylov, s5:fibre(b), r<kappa.
Proof: compare the true inverse solutions before and after the shift. The
nonnegative shifted energy of their actual difference bounds the inverse-form
increase below by mu times the original inverse solution's positive squared norm. -/
theorem shifted_inverse_quadratic_strict (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.PosDef)
    (mu : ℝ) (hmu : 0<mu) (hshift : (H-mu • 1).PosDef)
    (x : Fin p → ℝ) (hx : x≠0) :
    x ⬝ᵥ (H⁻¹*ᵥ x)<x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x) := by
  let B := H-mu • 1
  let y := H⁻¹*ᵥ x
  let u := B⁻¹*ᵥ x
  have hy : H*ᵥ y=x := by
    dsimp only [y]
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),one_mulVec]
  have hu : B*ᵥ u=x := by
    dsimp only [u]
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hshift.det_pos.ne'),one_mulVec]
  have hyn : y≠0 := by intro he;apply hx;rw [he,mulVec_zero] at hy;exact hy.symm
  have hyself : 0<y ⬝ᵥ y := by
    simpa only [star_trivial,one_mulVec] using
      (Matrix.PosDef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosDef).dotProduct_mulVec_pos hyn
  have hBy : B*ᵥ y=x-mu • y := by
    dsimp only [B]
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hy]
  have hcross : u ⬝ᵥ (B*ᵥ y)=x ⬝ᵥ y := by
    have he := hshift.1.star_dotProduct_mulVec_comm u y
    simp only [star_trivial] at he
    change u ⬝ᵥ (B*ᵥ y)=y ⬝ᵥ (B*ᵥ u) at he
    rw [hu] at he
    exact he.trans (dotProduct_comm y x)
  have henergy := hshift.posSemidef.dotProduct_mulVec_nonneg (u-y)
  simp only [star_trivial] at henergy
  change 0≤(u-y) ⬝ᵥ (B*ᵥ (u-y)) at henergy
  simp only [Matrix.mulVec_sub,dotProduct_sub,sub_dotProduct,hu] at henergy
  rw [hcross,hBy] at henergy
  simp only [dotProduct_sub,dotProduct_smul,smul_eq_mul,dotProduct_comm u x,dotProduct_comm y x] at henergy
  change x ⬝ᵥ y<x ⬝ᵥ u
  nlinarith [mul_pos hmu hyself]

end
end krylov.LinearAlgebra
