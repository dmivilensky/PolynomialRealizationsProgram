import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Jacobi's determinant derivative, including singular base matrices,
proved from the permutation expansion and Cramer's column formula. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open Matrix
open scoped BigOperators
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem det_updateCol_expansion (A B : Matrix n n ℝ) (j : n) :
    (A.updateCol j (fun i=>B i j)).det=
      ∑σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ)*
        ((∏k∈Finset.univ.erase j,A (σ k) k)*B (σ j) j) := by
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [←Finset.prod_erase_mul Finset.univ
    (fun k=>(A.updateCol j (fun i=>B i j)) (σ k) k) (Finset.mem_univ j)]
  simp only [Matrix.updateCol_apply,ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact ite_eq_right (Finset.ne_of_mem_erase hk)

/-- Jacobi formula in the exact column orientation needed by the source
transversality contraction. No nonsingularity assumption is imposed. -/
theorem hasDerivAt_det (M : ℝ→Matrix n n ℝ) (M' : Matrix n n ℝ) (t : ℝ)
    (h : ∀i j,HasDerivAt (fun x=>M x i j) (M' i j) t) :
    HasDerivAt (fun x=>(M x).det)
      (∑j,((M t).adjugate.mulVec (fun i=>M' i j)) j) t := by
  have hσ (σ : Equiv.Perm n) :=
    (HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun k _=>h (σ k) k)).const_mul
      (((Equiv.Perm.sign σ : ℤ) : ℝ))
  have hd := HasDerivAt.sum (u:=Finset.univ) (fun σ _=>hσ σ)
  have hform : (fun x=>(M x).det)=fun x=>
      ∑σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ)*(∏k,M x (σ k) k) := by
    funext x
    exact Matrix.det_apply' (M x)
  rw [hform]
  convert hd using 1
  · funext x
    simp only [Finset.sum_apply]
  · simp only [smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [←Matrix.cramer_eq_adjugate_mulVec,Matrix.cramer_apply,det_updateCol_expansion]

end polyak.ModeLocking.Continuation
