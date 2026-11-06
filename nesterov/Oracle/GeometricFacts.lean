import nesterov.Oracle.GeometricExtension
import nesterov.Oracle.GeometricScores
import nesterov.Oracle.GeometricStar

/-! Every geometric premise of the zero-chain and minimizer construction is
proved here for explicit finite data. -/
namespace nesterov.Oracle.Geometric
noncomputable section
open Set
open scoped RealInnerProductSpace

theorem data_ordered_scores (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    {j k : Fin (N+2)} (hjk : j.val≤k.val) (i : Fin (N+2)) :
    (data N s hs hs1).offsets k-
        inner ℝ ((data N s hs hs1).slopes k) ((data N s hs hs1).slopes i)/(1-(data N s hs hs1).q)≤
      (data N s hs hs1).offsets j-
        inner ℝ ((data N s hs hs1).slopes j) ((data N s hs hs1).slopes i)/(1-(data N s hs hs1).q) :=
  ordered_score_inequality hs hs1 hjk i

theorem data_slope_after (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (j : Fin (N+1)) (ℓ : Fin (N+1)) (h : j.val<ℓ.val) :
    (data N s hs hs1).slopes j.castSucc ℓ=0 := slope_after s h

theorem data_prefix_equal (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (j : Fin (N+1)) (k : Fin (N+2)) (ℓ : Fin (N+1))
    (hℓ : ℓ.val<j.val) (hjk : j.val<k.val) :
    (data N s hs hs1).slopes j.castSucc ℓ=(data N s hs hs1).slopes k ℓ := by
  change slope N s j.val ℓ=slope N s k.val ℓ
  rw [slope_before s hℓ,slope_before s (hℓ.trans hjk)]

theorem data_diagonal_strict (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (j : Fin (N+1)) (k : Fin (N+2)) (hjk : j.val<k.val) :
    (data N s hs hs1).slopes k j<(data N s hs hs1).slopes j.castSucc j := by
  change slope N s k.val j<slope N s j.val j
  rw [slope_before s hjk,slope_self]
  have hδ := delta_pos hs hs1 j.val
  nlinarith [mul_pos hδ (show 0<s-s^2 by nlinarith)]

theorem data_star_optimizer (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1) (i : Fin (N+2)) :
    inner ℝ ((data N s hs hs1).slopes i-(data N s hs hs1).slopes (Fin.last (N+1)))
      (starPoint N s-(1/(1-(data N s hs hs1).q)) • (data N s hs hs1).slopes (Fin.last (N+1)))+
        (data N s hs hs1).offsets i-(data N s hs hs1).offsets (Fin.last (N+1))≤0 := by
  change inner ℝ (slope N s i.val-slope N s (N+1))
    (starPoint N s-(1/(1-s^2)) • slope N s (N+1))+offset N s i.val-offset N s (N+1)≤0
  exact (star_score_equality hs hs1 i.val).le

theorem data_stationary (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    (data N s hs hs1).q • starPoint N s+(data N s hs hs1).slopes (Fin.last (N+1))=0 :=
  star_stationary N s

theorem data_starPoint_norm (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    ‖starPoint N s‖≤1 := starPoint_norm_le hs hs1

end
end nesterov.Oracle.Geometric
