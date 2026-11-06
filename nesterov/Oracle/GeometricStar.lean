import nesterov.Oracle.GeometricAdjacent

/-! The concrete geometric star satisfies every exact optimizer score and
has a nonzero hidden terminal coordinate. -/
namespace nesterov.Oracle.Geometric
noncomputable section
open Finset Set
open scoped BigOperators RealInnerProductSpace

def adjustedHeight (N : ℕ) (s : ℝ) (j : ℕ) : ℝ :=
  (1-s^2)*offset N s j+inner ℝ (slope N s j) (starPoint N s)

theorem adjustedHeight_succ {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1) (j : ℕ) :
    adjustedHeight N s (j+1)=adjustedHeight N s j := by
  have he : (1-s^2)*(offset N s j-offset N s (j+1))+
      inner ℝ (slope N s j-slope N s (j+1)) (starPoint N s)=0 := by
    rcases lt_trichotomy j N with hj|hj|hj
    · rw [slope_adjacent s hj,real_inner_smul_left,inner_sub_left,
        EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_left,
        offset_adjacent hs hs1 hj]
      simp only [map_one,one_mul,starPoint_apply]
      rw [delta_succ]
      unfold rho
      ring
    · subst j
      rw [slope_last,real_inner_smul_left,EuclideanSpace.inner_single_left,offset_last N hs hs1]
      simp only [map_one,one_mul,starPoint_apply,Fin.val_last]
      ring
    · rw [slope_tail_constant s (show N+1≤j by omega),
        slope_tail_constant s (show N+1≤j+1 by omega),sub_self,inner_zero_left]
      simp only [offset,show ¬j<N+1 by omega,show ¬j+1<N+1 by omega,ite_false,sub_self,mul_zero,add_zero]
  rw [inner_sub_left] at he
  unfold adjustedHeight
  linarith

theorem adjustedHeight_constant {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1) (j k : ℕ) :
    adjustedHeight N s j=adjustedHeight N s k := by
  have h (j : ℕ) : adjustedHeight N s j=adjustedHeight N s 0 := by
    induction j with
    | zero => rfl
    | succ j ih => exact (adjustedHeight_succ hs hs1 j).trans ih
  exact (h j).trans (h k).symm

theorem star_score_numerator {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1) (j : ℕ) :
    inner ℝ (slope N s j-slope N s (N+1)) (starPoint N s)+
      (1-s^2)*(offset N s j-offset N s (N+1))=0 := by
  have h := adjustedHeight_constant (N:=N) hs hs1 j (N+1)
  unfold adjustedHeight at h
  rw [inner_sub_left]
  linarith

theorem star_score_equality {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1) (j : ℕ) :
    inner ℝ (slope N s j-slope N s (N+1))
      (starPoint N s-(1/(1-s^2)) • slope N s (N+1))+
        offset N s j-offset N s (N+1)=0 := by
  have ha : 1-s^2≠0 := by nlinarith
  have hvector : starPoint N s-(1/(1-s^2)) • slope N s (N+1)=
      (1/(1-s^2)) • starPoint N s := by
    ext ℓ
    simp only [PiLp.sub_apply,PiLp.smul_apply,starPoint_apply,slope_star,smul_eq_mul]
    field_simp
    ring
  rw [hvector,real_inner_smul_right]
  have h := star_score_numerator (N:=N) hs hs1 j
  have hh : (1/(1-s^2))*inner ℝ (slope N s j-slope N s (N+1)) (starPoint N s)+
      offset N s j-offset N s (N+1)=
      (inner ℝ (slope N s j-slope N s (N+1)) (starPoint N s)+
        (1-s^2)*(offset N s j-offset N s (N+1)))/(1-s^2) := by field_simp;ring
  rw [hh,h,zero_div]

theorem star_terminal_coordinate (N : ℕ) (s : ℝ) :
    starPoint N s (Fin.last N)= -delta s N := rfl

end
end nesterov.Oracle.Geometric
