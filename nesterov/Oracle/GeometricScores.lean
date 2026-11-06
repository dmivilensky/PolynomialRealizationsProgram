import nesterov.Oracle.GeometricAdjacent

/-! The actual finite geometric data satisfy all ordered slope-score
inequalities needed for the zero-chain faces. -/
namespace nesterov.Oracle.Geometric
noncomputable section
open Finset Set
open scoped BigOperators RealInnerProductSpace

def score (N : ℕ) (s : ℝ) (i j : ℕ) : ℝ :=
  offset N s j-inner ℝ (slope N s j) (slope N s i)/(1-s^2)

theorem score_succ_le {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1) (i j : ℕ) :
    score N s i (j+1)≤score N s i j := by
  have ha : 0<1-s^2 := by nlinarith
  have hρ := rho_pos hs1
  have hinner : inner ℝ (slope N s j-slope N s (j+1)) (slope N s i)≤
      (1-s^2)*(offset N s j-offset N s (j+1)) := by
    rcases lt_trichotomy j N with hj|hj|hj
    · rw [slope_adjacent s hj,real_inner_smul_left,inner_sub_left,
        EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_left,
        offset_adjacent hs hs1 hj]
      simp only [map_one,one_mul]
      have hb0 := (slope_bounds hs hs1 i (⟨j,Nat.lt_trans hj (Nat.lt_succ_self N)⟩ : Fin (N+1))).2
      have hb1 := (slope_bounds hs hs1 i (⟨j+1,Nat.succ_lt_succ hj⟩ : Fin (N+1))).1
      exact mul_le_mul_of_nonneg_left (by linarith :
        slope N s i ⟨j,Nat.lt_trans hj (Nat.lt_succ_self N)⟩-slope N s i ⟨j+1,Nat.succ_lt_succ hj⟩≤s*delta s j)
        (mul_nonneg hs.le (delta_pos hs hs1 (j+1)).le)
    · subst j
      rw [slope_last,real_inner_smul_left,EuclideanSpace.inner_single_left,offset_last N hs hs1]
      simp only [map_one,one_mul]
      have hb := (slope_bounds hs hs1 i (Fin.last N)).2
      have hδ := delta_pos hs hs1 N
      have hb' : slope N s i (Fin.last N)≤delta s N := by
        dsimp only [Fin.val_last] at hb
        nlinarith
      have hm := mul_le_mul_of_nonneg_left hb' (by positivity : 0≤s*rho s*delta s N)
      nlinarith only [hm]
    · have h0 : N+1≤j := by omega
      have h1 : N+1≤j+1 := by omega
      rw [slope_tail_constant s h0,slope_tail_constant s h1,sub_self,inner_zero_left]
      simp only [offset,not_lt.mpr h0,not_lt.mpr h1,ite_false,sub_self,mul_zero,le_refl]
  rw [inner_sub_left] at hinner
  have hdiv : (inner ℝ (slope N s j) (slope N s i)-
      inner ℝ (slope N s (j+1)) (slope N s i))/(1-s^2)≤
        offset N s j-offset N s (j+1) := (div_le_iff₀ ha).mpr (by nlinarith only [hinner])
  rw [sub_div] at hdiv
  unfold score
  linarith

theorem score_antitone {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1) (i : ℕ) :
    Antitone (score N s i) := antitone_nat_of_succ_le (score_succ_le hs hs1 i)

theorem ordered_score_inequality {N : ℕ} {s : ℝ} (hs : 0<s) (hs1 : s<1)
    {j k : Fin (N+2)} (hjk : j.val≤k.val) (i : Fin (N+2)) :
    offset N s k.val-inner ℝ (slope N s k.val) (slope N s i.val)/(1-s^2)≤
      offset N s j.val-inner ℝ (slope N s j.val) (slope N s i.val)/(1-s^2) :=
  score_antitone hs hs1 i.val hjk

end
end nesterov.Oracle.Geometric
