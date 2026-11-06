import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import nesterov.IQC.KYP.QuadraticMaximum

/-! Transfer of finite real quadratic inequalities to every real Hilbert space. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators MatrixOrder InnerProductSpace
variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixInner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Matrix I I ℝ) (x y : I→E) : ℝ:=∑ i,∑ j,A i j*inner ℝ (x i) (y j)

theorem matrixInner_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : Matrix I I ℝ} (hA : A.PosSemidef) (x : I→E) : 0≤matrixInner A x x := by
  have hf : ∃ B : Matrix I I ℝ,A=B.transpose*B := by
    let B:=CFC.sqrt A
    have hs : star B=B:=IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
    refine ⟨B,?_⟩
    have hh:=CFC.sqrt_mul_sqrt_self A hA.nonneg
    change B*B=A at hh
    rw [←hh]
    congr 1
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hs.symm
  obtain ⟨B,hB⟩:=hf
  rw [hB]
  have he : matrixInner (B.transpose*B) x x=∑ k,‖∑ i,B k i • x i‖^2 := by
    unfold matrixInner
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    calc
      _=∑ i,∑ k,∑ j,(B k i*B k j)*inner ℝ (x i) (x j):=by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _=∑ k,∑ i,∑ j,(B k i*B k j)*inner ℝ (x i) (x j):=Finset.sum_comm
      _=_:=by
        apply Finset.sum_congr rfl
        intro k _
        rw [←real_inner_self_eq_norm_sq]
        simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [real_inner_comm (x j) (x i)]
        ring
  rw [he]
  exact Finset.sum_nonneg (fun _ _=>sq_nonneg _)

/-- Matrix of a real finite-state bounded bilinear form. -/
def bilinearMatrix (B : Bilinear (I→ℝ)) : Matrix I I ℝ:=
  fun i j=>B (Pi.single i 1) (Pi.single j 1)

theorem bilinearMatrix_apply (B : Bilinear (I→ℝ)) (x y : I→ℝ) :
    B x y=∑ i,∑ j,bilinearMatrix B i j*x i*y j := by
  have hx : x=∑ i,x i • (Pi.single i (1:ℝ):I→ℝ) := by
    ext j
    simp [Pi.single_apply,mul_ite]
  have hy : y=∑ i,y i • (Pi.single i (1:ℝ):I→ℝ) := by
    ext j
    simp [Pi.single_apply,mul_ite]
  have hfirst:=congrArg (fun z : I→ℝ=>B z y) hx
  simp only [map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul] at hfirst
  have hsecond (i : I) : B (Pi.single i 1) y=∑ j,y j*B (Pi.single i 1) (Pi.single j 1) := by
    have hh:=congrArg (fun z : I→ℝ=>B (Pi.single i 1) z) hy
    simpa only [map_sum,map_smul,smul_eq_mul] using hh
  rw [hfirst]
  simp_rw [hsecond]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [bilinearMatrix]
  ring

theorem bilinearMatrix_posSemidef (B : Bilinear (I→ℝ))
    (hs : ∀ x y,B x y=B y x) (hp : ∀ x,0≤B x x) : (bilinearMatrix B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial,bilinearMatrix]
    exact hs _ _
  · intro x
    have hh:=hp x
    rw [bilinearMatrix_apply] at hh
    simpa only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum,mul_assoc,mul_left_comm] using hh

/-- Every scalar finite quadratic inequality acts with the same coefficients
on arbitrary real Hilbert vectors. -/
theorem tensor_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : Bilinear (I→ℝ)) (hs : ∀ x y,B x y=B y x) (hp : ∀ x,0≤B x x) (x : I→E) :
    0≤matrixInner (bilinearMatrix B) x x:=matrixInner_nonneg (bilinearMatrix_posSemidef B hs hp) x

end
end nesterov.IQC.KYP
