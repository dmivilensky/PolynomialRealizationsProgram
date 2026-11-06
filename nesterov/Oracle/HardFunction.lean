import nesterov.Oracle.GeometricExtension
import nesterov.Oracle.GeometricScores
import nesterov.Oracle.GeometricStar
import nesterov.Oracle.ExtensionZeroChain
import nesterov.Oracle.ExtensionMinimum

/-! The actual normalized hard function: smooth strongly convex,
with its verified hidden minimizer and first-order zero-chain property. -/
namespace nesterov.Oracle.Geometric
noncomputable section
open Set
variable (N : ℕ) {s : ℝ} (hs : 0<s) (hs1 : s<1)

def hardFunction : ChainSpace N→ℝ := (data N s hs hs1).potential

theorem hardFunction_class : polyak.SmoothStronglyConvex (s^2) 1 (hardFunction N hs hs1) :=
  (data N s hs hs1).smoothStronglyConvex

theorem star_maximum_scores (i : Fin (N+2)) :
    (data N s hs hs1).score (starPoint N s) (Pi.single (Fin.last (N+1)) 1) i≤
      (data N s hs hs1).score (starPoint N s) (Pi.single (Fin.last (N+1)) 1) (Fin.last (N+1)) := by
  simp only [ExtensionData.score,moment_single]
  change inner ℝ (slope N s i.val)
      (starPoint N s-(1/(1-s^2)) • slope N s (N+1))+offset N s i.val≤
    inner ℝ (slope N s (N+1))
      (starPoint N s-(1/(1-s^2)) • slope N s (N+1))+offset N s (N+1)
  have h := star_score_equality (N:=N) hs hs1 i.val
  rw [inner_sub_left] at h
  linarith

theorem hardFunction_stationary : gradient (hardFunction N hs hs1) (starPoint N s)=0 := by
  exact (data N s hs hs1).stationary_of_single_scores (starPoint N s) (Fin.last (N+1))
    (star_maximum_scores N hs hs1) (star_stationary N s)

theorem hardFunction_minimum : IsMinOn (hardFunction N hs hs1) univ (starPoint N s) :=
  (data N s hs hs1).isMinOn_of_single_scores (starPoint N s) (Fin.last (N+1))
    (star_maximum_scores N hs hs1) (star_stationary N s)

theorem hardFunction_zero_chain {j : Fin (N+1)} {y : ChainSpace N}
    (hy : ∀ m : Fin (N+1),j.val≤m.val →y m=0) :
    ∀ m : Fin (N+1),j.val<m.val →(data N s hs hs1).field y m=0 := by
  apply (data N s hs hs1).zero_chain
  · intro j k hk i
    exact ordered_score_inequality hs hs1 hk.le i
  · intro j m hjm
    exact slope_after s hjm
  · intro j k hjk m hmj
    change slope N s j.val m=slope N s k.val m
    rw [slope_before s hmj,slope_before s (hmj.trans hjk)]
  · intro j k hjk
    change 0<slope N s j.val j-slope N s k.val j
    rw [slope_self,slope_before s hjk]
    have h := mul_pos (mul_pos hs (sub_pos.mpr hs1)) (delta_pos hs hs1 j.val)
    nlinarith
  · exact hy

theorem hardFunction_support_zero_chain {j : Fin (N+1)} {y : ChainSpace N}
    (hy : ∀ m : Fin (N+1),j.val≤m.val →y m=0) :
    ∀ m : Fin (N+1),j.val<m.val →(data N s hs hs1).support y m=0 := by
  intro m hm
  have h := hardFunction_zero_chain N hs hs1 hy m hm
  change s^2*y m+(data N s hs hs1).support y m=0 at h
  rwa [hy m hm.le,mul_zero,zero_add] at h

end
end nesterov.Oracle.Geometric
