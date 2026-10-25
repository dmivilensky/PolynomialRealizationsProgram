import polyak.ModeLocking.Continuation.LeftKernel
import polyak.ModeLocking.Continuation.Determinant
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The literal adjugate at a regular point is a nonzero product of the
positive right and left kernel vectors. No cofactor nondegeneracy is assumed. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem matrix_det_zero : D.matrix.det=0 := by
  by_contra hn
  apply D.primal_ne_zero
  apply Matrix.mulVec_injective_of_det_ne_zero hn
  simpa only [Matrix.mulVec_zero] using D.matrix_mul_primal

private theorem left_column_zero (j : Fin D.d) :
    (∑ r, D.classWeight r*D.matrix r j)=0 := by
  have hh := congrFun D.matrix_transpose_mul_classWeight j
  simpa only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,Pi.zero_apply,mul_comm] using hh

/-- Replacing any column by a transverse vector gives an invertible matrix.
This proves the nonzero cofactor assertion directly from the primary data. -/
theorem transverse_updateCol_injective (b : Fin D.d → ℝ)
    (hb : (∑ r, D.classWeight r*b r)≠0) (j : Fin D.d) :
    Function.Injective (D.matrix.updateCol j b).mulVec := by
  classical
  apply (injective_iff_map_eq_zero (D.matrix.updateCol j b).mulVecLin).mpr
  intro v hv
  change (D.matrix.updateCol j b).mulVec v=0 at hv
  have hsum : (∑ r, D.classWeight r*((D.matrix.updateCol j b).mulVec v r)) =
      (∑ r, D.classWeight r*b r)*v j := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm (i : Fin D.d) :
        (∑ r,D.classWeight r*((D.matrix.updateCol j b) r i*v i)) =
          if i=j then (∑ r,D.classWeight r*b r)*v j else 0 := by
      by_cases hij : i=j
      · subst i
        simp only [Matrix.updateCol_apply,ite_true,Finset.sum_mul,mul_assoc]
      · simp only [Matrix.updateCol_apply,ite_eq_right hij]
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul,D.left_column_zero i,zero_mul]
    simp only [hterm,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hz : v j=0 := by
    rw [hv] at hsum
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hsum
    exact (mul_eq_zero.mp hsum.symm).resolve_left hb
  have hAv : D.matrix.mulVec v=0 := by
    rw [← hv]
    funext r
    change (∑ i,D.matrix r i*v i) = ∑ i,(D.matrix.updateCol j b) r i*v i
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i=j
    · subst i
      rw [hz,mul_zero,mul_zero]
    · rw [Matrix.updateCol_apply,ite_eq_right hij]
  obtain ⟨c,hc⟩ := D.kernel_unique hAv
  have hp : (D.primal j:ℝ)≠0 := by exact_mod_cast (D.primal_pos j).ne'
  have hcz : c=0 := (mul_eq_zero.mp ((hc j).symm.trans hz)).resolve_right hp
  funext i
  change v i=0
  rw [hc i,hcz,zero_mul]

theorem transverse_updateCol_det_ne_zero (b : Fin D.d → ℝ)
    (hb : (∑ r,D.classWeight r*b r)≠0) (j : Fin D.d) :
    (D.matrix.updateCol j b).det≠0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (D.transverse_updateCol_injective b hb j))).ne_zero

theorem adjugate_mul_shift_ne_zero : D.matrix.adjugate.mulVec D.shiftVector≠0 := by
  intro hz
  have j : Fin D.d := ⟨0,D.d_pos⟩
  have hh := congrFun hz j
  rw [← Matrix.cramer_eq_adjugate_mulVec,Matrix.cramer_apply] at hh
  exact D.transverse_updateCol_det_ne_zero D.shiftVector D.transversality_pos.ne' j hh

theorem adjugate_ne_zero : D.matrix.adjugate≠0 := by
  intro hz
  apply D.adjugate_mul_shift_ne_zero
  rw [hz,Matrix.zero_mulVec]

/-- The source's nonzero scalar factor c in adj(M)=c w mu^T. -/
theorem adjugate_factor : ∃ c : ℝ, c≠0 ∧
    ∀ i j, D.matrix.adjugate i j=c*(D.primal i:ℝ)*D.classWeight j := by
  have hcols (j : Fin D.d) : D.matrix.mulVec (fun i => D.matrix.adjugate i j)=0 := by
    have hh := congrArg (fun A : Matrix (Fin D.d) (Fin D.d) ℝ => fun i => A i j)
      (Matrix.mul_adjugate D.matrix)
    funext i
    simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct,D.matrix_det_zero,
      zero_smul,Matrix.zero_apply,Pi.zero_apply] using congrFun hh i
  choose v hv using fun j => D.kernel_unique (hcols j)
  have hrow : D.matrix.transpose.mulVec v=0 := by
    let i : Fin D.d := ⟨0,D.d_pos⟩
    have hp : (D.primal i:ℝ)≠0 := by exact_mod_cast (D.primal_pos i).ne'
    funext j
    have hh := congrArg (fun A : Matrix (Fin D.d) (Fin D.d) ℝ => A i j)
      (Matrix.adjugate_mul D.matrix)
    simp only [Matrix.mul_apply,D.matrix_det_zero,zero_smul,Matrix.zero_apply] at hh
    simp_rw [hv] at hh
    have he : (∑ k,v k*(D.primal i:ℝ)*D.matrix k j) =
        (D.primal i:ℝ)*(D.matrix.transpose.mulVec v j) := by
      simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he] at hh
    exact (mul_eq_zero.mp hh).resolve_left hp
  obtain ⟨c,hc⟩ := D.left_kernel_unique hrow
  have hfactor (i j : Fin D.d) : D.matrix.adjugate i j=c*(D.primal i:ℝ)*D.classWeight j := by
    rw [hv j i,hc j]
    ring
  refine ⟨c,?_,hfactor⟩
  intro hcz
  apply D.adjugate_ne_zero
  ext i j
  rw [hfactor,hcz,zero_mul,zero_mul,Matrix.zero_apply]

theorem adjugate_contraction_factor (B : Matrix (Fin D.d) (Fin D.d) ℝ) :
    ∃ c : ℝ, c≠0 ∧ (∑ j,(D.matrix.adjugate.mulVec (fun i => B i j)) j) =
      c*(∑ r,D.classWeight r*(∑ i,B r i*(D.primal i:ℝ))) := by
  obtain ⟨c,hc,hfactor⟩ := D.adjugate_factor
  refine ⟨c,hc,?_⟩
  simp only [Matrix.mulVec,dotProduct,hfactor]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

end polyak.ModeLocking.RegularData
