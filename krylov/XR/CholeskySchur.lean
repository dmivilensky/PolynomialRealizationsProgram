import krylov.XR.WindowTest
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Article: main_krylov, prop:cert, actual Hermitian Cholesky pivot domain.
Use: justify the strict Schur-pivot test used when a reversed window is
extended by one actual column. Source: mathlib's exact Hermitian quadratic
Schur-complement identity; positivity is derived, not provided as a pivot
certificate.
-/
namespace krylov.XR
noncomputable section
open Matrix
open scoped ComplexOrder Matrix
variable {m n : ℕ}

/-- Strict Hermitian Schur-complement positivity on its genuine positive
leading-block domain. This is the exact algebraic Cholesky extension
criterion, including empty leading blocks. Article: prop:cert. -/
theorem posDef_fromBlocks_schur (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (fromBlocks A B Bᴴ D).PosDef ↔ (D-Bᴴ*A⁻¹*B).PosDef := by
  let := invertibleOfIsUnitDet A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  constructor
  · intro h
    refine PosDef.of_dotProduct_mulVec_pos ((IsHermitian.fromBlocks₁₁ B D hA.1).mp h.1) ?_
    intro y hy
    let x := -((A⁻¹*B)*ᵥ y)
    have hxy : (x ⊕ᵥ y)≠0 := by
      intro hz
      apply hy
      funext i
      exact congrFun hz (Sum.inr i)
    have hh := h.dotProduct_mulVec_pos hxy
    rw [dotProduct_mulVec,schur_complement_eq₁₁ B D x y hA.1] at hh
    simpa only [x,neg_add_cancel,star_zero,zero_vecMul,zero_dotProduct,zero_add,
      dotProduct_mulVec] using hh
  · intro h
    refine PosDef.of_dotProduct_mulVec_pos ((IsHermitian.fromBlocks₁₁ B D hA.1).mpr h.1) ?_
    intro v hv
    rw [dotProduct_mulVec,←Sum.elim_comp_inl_inr v,
      schur_complement_eq₁₁ B D (v ∘ Sum.inl) (v ∘ Sum.inr) hA.1]
    by_cases hy : v ∘ Sum.inr=0
    · have hx : v ∘ Sum.inl≠0 := by
        intro hx
        apply hv
        funext i
        cases i with
        | inl i => exact congrFun hx i
        | inr i => exact congrFun hy i
      simpa only [hy,mulVec_zero,add_zero,star_zero,zero_vecMul,zero_dotProduct,
        add_zero,dotProduct_mulVec] using hA.dotProduct_mulVec_pos hx
    · have hp := h.dotProduct_mulVec_pos hy
      have hn := hA.posSemidef.dotProduct_mulVec_nonneg
        ((v ∘ Sum.inl)+(A⁻¹*B)*ᵥ (v ∘ Sum.inr))
      rw [dotProduct_mulVec] at hn hp
      exact add_pos_of_nonneg_of_pos hn hp

/-- A one-dimensional Hermitian Schur block is positive exactly when
its actual scalar pivot is positive. Article: main_krylov, prop:cert. -/
theorem posDef_fin_one_iff (A : Matrix (Fin 1) (Fin 1) ℂ) : A.PosDef ↔ 0<A 0 0 := by
  have he : A=diagonal (fun _ : Fin 1=>A 0 0) := by ext i j; fin_cases i; fin_cases j; rfl
  rw [he,Matrix.posDef_diagonal_iff]
  exact ⟨fun h=>h 0,fun h _=>h⟩

/-- The actual squared Cholesky pivot for appending one original column.
No diagonal-root choice is involved in its sign. Article: prop:cert. -/
def schurPivot (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin 1) ℂ) (D : Matrix (Fin 1) (Fin 1) ℂ) : ℂ :=
  (D-Bᴴ*A⁻¹*B) 0 0

/-- The actual extension passes the original Hermitian test exactly
when its genuine next Schur/Cholesky pivot is positive.
Article: main_krylov, prop:cert. -/
theorem cholesky_extension_iff (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin 1) ℂ) (D : Matrix (Fin 1) (Fin 1) ℂ) (hA : A.PosDef) :
    (fromBlocks A B Bᴴ D).PosDef ↔ 0<schurPivot A B D := by
  rw [posDef_fromBlocks_schur A B D hA,posDef_fin_one_iff]
  rfl

end
end krylov.XR
