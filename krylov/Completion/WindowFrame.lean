import krylov.Completion.CurvatureCompletion
import krylov.LinearAlgebra.HiddenEntry
import Mathlib.Data.Matrix.ColumnRowPartitioned
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, actual arbitrary-window coordinates.
Use: derive the positive augmented Gram from the source's independent stored
window and genuinely new direction, instead of assuming a completion frame.
Source: elementary full-column-rank Gram positivity and physical block multiplication.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- The actual new direction followed by the original stored physical window.
Use: the completion frame is constructed directly from the source data.
Article: main_krylov, thm:radau.
Proof: prepend the physical direction as a single column. -/
def curvatureFrame (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin 1 ⊕ Fin p) ℝ := fromCols (crossColumn d) S

/-- The actual augmented physical frame has its literal Euclidean Gram blocks.
Use: the scalar Schur interval uses SᵀS, Sᵀd and the real squared direction norm.
Article: main_krylov, thm:radau.
Proof: multiply the true column-partitioned frame and its transpose. -/
theorem curvature_frame_gram (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) :
    (curvatureFrame S d)ᵀ*curvatureFrame S d=
      windowAugmentedGram (Sᵀ*S) (Sᵀ*crossColumn d) (d ⬝ᵥ d) := by
  rw [curvatureFrame,transpose_fromCols,fromRows_mul_fromCols]
  have hscalar : (crossColumn d)ᵀ*crossColumn d=scalarCorner (d ⬝ᵥ d) := by
    ext i j
    rfl
  have hcross : (crossColumn d)ᵀ*S=(Sᵀ*crossColumn d)ᵀ := by
    simp only [transpose_mul,transpose_transpose]
  rw [hscalar,hcross]
  rfl

/-- Independent old columns and a direction outside their span give a genuinely
positive augmented physical Gram, with no assumed reconstruction domain.
Use: discharge the full-rank frame premise of physical spectral completion
from precisely the original arbitrary-window hypotheses.
Article: main_krylov, thm:radau.
Proof: a null combination with a nonzero new-direction coefficient would put
the direction in the old range. Its coefficient is therefore zero, and actual
old-column independence kills the remaining coefficients. -/
theorem curvature_frame_positive (S : Matrix (Fin n) (Fin p) ℝ)
    (hS : Function.Injective S.mulVec) (d : Fin n → ℝ)
    (hd : d∉LinearMap.range S.mulVecLin) :
    ((curvatureFrame S d)ᵀ*curvatureFrame S d).PosDef := by
  have hinj : Function.Injective (curvatureFrame S d).mulVec := by
    apply (LinearMap.ker_eq_bot (f := (curvatureFrame S d).mulVecLin)).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have he : (curvatureFrame S d)*ᵥ x=x (Sum.inl 0) • d+S*ᵥ (x ∘ Sum.inr) := by
      rw [curvatureFrame,fromCols_mulVec]
      congr 1
      ext i
      simp only [mulVec,crossColumn,dotProduct,Fin.sum_univ_one,Function.comp_apply,
        Pi.smul_apply,smul_eq_mul,mul_comm]
    change (curvatureFrame S d)*ᵥ x=0 at hx
    rw [he] at hx
    have hc : x (Sum.inl 0)=0 := by
      by_contra hn
      apply hd
      refine ⟨(-((x (Sum.inl 0))⁻¹)) • (x ∘ Sum.inr),?_⟩
      change S*ᵥ (-((x (Sum.inl 0))⁻¹) • (x ∘ Sum.inr))=d
      have hs : S*ᵥ (x ∘ Sum.inr)= -(x (Sum.inl 0) • d) := by
        exact eq_neg_of_add_eq_zero_right hx
      rw [mulVec_smul,hs,smul_neg,smul_smul,neg_mul,inv_mul_cancel₀ hn,neg_smul,neg_neg,one_smul]
    rw [hc,zero_smul,zero_add] at hx
    have hv : x ∘ Sum.inr=0 := hS (hx.trans (Matrix.mulVec_zero S).symm)
    funext i
    cases i with
    | inl i => fin_cases i;exact hc
    | inr i => exact congrFun hv i
  simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.PosDef.conjTranspose_mul_self _ hinj

end
end krylov.Completion
