import nesterov.Oracle.GeometricData

/-! Adjacent differences of the concrete geometric slope and height data. -/
namespace nesterov.Oracle.Geometric
noncomputable section
open Finset Set
open scoped BigOperators RealInnerProductSpace

theorem slope_adjacent {N : ℕ} (s : ℝ) {j : ℕ} (hj : j<N) :
    slope N s j-slope N s (j+1)= (s*delta s (j+1)) •
      (EuclideanSpace.single (⟨j,by omega⟩ : Fin (N+1)) (1:ℝ)-EuclideanSpace.single (⟨j+1,by omega⟩ : Fin (N+1)) (1:ℝ)) := by
  ext ℓ
  simp only [PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply,smul_eq_mul]
  rw [slope_apply,slope_apply]
  have h0 : (ℓ=⟨j,by omega⟩)↔ℓ.val=j := Fin.ext_iff
  have h1 : (ℓ=⟨j+1,by omega⟩)↔ℓ.val=j+1 := Fin.ext_iff
  simp only [h0,h1]
  rcases lt_trichotomy ℓ.val j with h|h|h
  · simp only [h,show ℓ.val<j+1 by omega,ite_true,ne_of_lt h,ite_false,
      show ¬ℓ.val=j+1 by omega,sub_self,mul_zero]
  · simp only [h,lt_self_iff_false,ite_false,ite_true,Nat.lt_succ_self,sub_zero,mul_one,
      show ¬j=j+1 by omega]
    rw [delta_succ]
    unfold rho
    ring
  · by_cases he : ℓ.val=j+1
    · simp [he]
    · simp only [show ¬ℓ.val<j by omega,show ¬ℓ.val<j+1 by omega,ne_of_gt h,he,
        ite_false,sub_self,mul_zero]

theorem slope_last (N : ℕ) (s : ℝ) :
    slope N s N-slope N s (N+1)= (s*rho s*delta s N) •EuclideanSpace.single (Fin.last N) (1:ℝ) := by
  ext ℓ
  simp only [PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply,smul_eq_mul]
  rw [slope_apply,slope_star]
  by_cases h : ℓ.val=N
  · have he : ℓ=Fin.last N := Fin.ext h
    simp only [he,Fin.val_last,lt_self_iff_false,ite_false,ite_true,mul_one]
    unfold rho
    ring
  · have hlt : ℓ.val<N := by omega
    have he : ℓ≠Fin.last N := by intro hh;apply h;exact congrArg Fin.val hh
    simp only [hlt,ite_true,sub_self,he,ite_false,mul_zero]

theorem offset_adjacent {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1)
    {j : ℕ} (hj : j<N) :
    (1-s^2)*(offset N s j-offset N s (j+1))=s*delta s (j+1)*(s*delta s j) := by
  simp only [offset,show j<N+1 by omega,show j+1<N+1 by omega,ite_true]
  rw [ordinary_offset_succ hs hs1]
  have hd : 1-s^2≠0 := by nlinarith
  field_simp

theorem offset_last (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    (1-s^2)*(offset N s N-offset N s (N+1))=s*rho s*delta s N^2 := by
  simp only [offset,Nat.lt_succ_self,ite_true,lt_self_iff_false,ite_false]
  rw [offset_star_identity hs hs1 N N,delta_sq hs hs1,pow_succ]
  unfold rho
  ring

end
end nesterov.Oracle.Geometric
