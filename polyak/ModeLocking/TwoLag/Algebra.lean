import polyak.ModeLocking.TwoLag.Pinning

/-! The positive rank-one primal/dual matrix forced by E1. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Matrix

theorem rank_one_of_positive_dual {A B C D a b : ℝ}
    (hA : 0<A) (hb : 0<b) (h₁ : a*A+b*C=0) (h₂ : a*B+b*D=0) :
    Matrix.rank (!![A,B;C,D] : Matrix (Fin 2) (Fin 2) ℝ)=1 := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![A,B;C,D]
  have ho : M=Matrix.vecMulVec (![1,-a/b] : Fin 2→ℝ) (![A,B] : Fin 2→ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [M, Matrix.vecMulVec]
    · simp [M, Matrix.vecMulVec]
    · change C=(-a/b)*A
      field_simp
      nlinarith [h₁]
    · change D=(-a/b)*B
      field_simp
      nlinarith [h₂]
  have hu : M.rank≤1 := by rw [ho]; exact Matrix.rank_vecMulVec_le _ _
  have hl : 1≤M.rank := by
    have hs := Matrix.rank_submatrix_le M (fun _ : Fin 1=>(0 : Fin 2)) (fun _ : Fin 1=>(0 : Fin 2))
    have hdet : Matrix.det (M.submatrix (fun _ : Fin 1=>(0 : Fin 2)) (fun _ : Fin 1=>(0 : Fin 2)))≠0 := by
      simpa [M, Matrix.det_fin_one] using hA.ne'
    rw [Matrix.rank_of_det_ne_zero hdet] at hs
    simpa using hs
  exact le_antisymm hu hl

theorem positive_primal_kernel {A B C D a b : ℝ}
    (hA : 0<A) (hB : B<0) (hb : 0<b)
    (h₁ : a*A+b*C=0) (h₂ : a*B+b*D=0) :
    0<(-B)/(A-B) ∧ 0<A/(A-B) ∧ (-B)/(A-B)+A/(A-B)=1 ∧
      (!![A,B;C,D] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![(-B)/(A-B),A/(A-B)]=0 := by
  have hd : 0<A-B := by linarith
  have hdet : A*D-B*C=0 := by
    have h : b*(A*D-B*C)=0 := by linear_combination A*h₂-B*h₁
    exact (mul_eq_zero.mp h).resolve_left hb.ne'
  refine ⟨div_pos (neg_pos.mpr hB) hd, div_pos hA hd, ?_, ?_⟩
  · field_simp; ring
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · field_simp; ring
    · field_simp
      nlinarith [hdet]

end polyak.ModeLocking.TwoLag
