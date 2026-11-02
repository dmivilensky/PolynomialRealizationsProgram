import krylov.Convergence.WindowCenteredCoordinates

/-!
Article: main_krylov, thm:ss1F and cor:xrF, arbitrary actual split coordinates.
Use: carry a genuine full value-model executor through the true positive
root without falsely claiming that Euclidean splitting is affine invariant.
The split policy is pulled back explicitly, preserving its observed values.
Source: exact affine trapezoid invariance and the full-model query identity.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The original actual split policy, expressed in centered metric data. -/
def centeredSplit (T : E ≃L[ℝ] E) (c : E)
    (split : (Fin (n+2) → E) → Fin (n+1) → ℝ)
    (q : Fin (n+2) → E) : Fin (n+1) → ℝ := split (fun i=>c+T.symm (q i))

/-- The actual split remainder is a primal vector under centering and
linear coordinate change; the original scalar split is retained. -/
theorem splitRemainder_centered_coordinate (T : E ≃L[ℝ] E) (c a s x : E) (l : ℝ) :
    T (splitRemainder a s x l)=splitRemainder (T (a-c)) (T s) (T (x-c)) l := by
  simp only [splitRemainder,map_sub,map_add,map_smul]
  module

/-- Full value queries transform with their same true scalar split
values, for arbitrary splits and genuine physical endpoint data. -/
theorem ss1FPoint_centered_coordinate {p : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (c : E) (f : E → ℝ) (G : E → E)
    (a s : Fin p → E) (l : Fin p → ℝ) (x : E) :
    T (ss1FPoint f G a s l x-c)=ss1FPoint (centeredMetricObjective T c f)
      (centeredMetricGradient T c G) (fun i=>T (a i-c)) (fun i=>T (s i)) l (T (x-c)) := by
  have hp : ss1FPoint (fun z=>f (c+z)) (fun z=>G (c+z)) (fun i=>a i-c) s l (x-c)=
      ss1FPoint f G a s l x-c := by
    simp only [ss1FPoint,valueCorrectedModel_translate,
      show c+(x-c)=x by abel]
    abel_nf
  rw [←hp]
  exact ss1FPoint_coordinate T hT _ _ _ _ _ _

/-- The literal full window rule transforms under the explicitly
pulled-back policy, without a split-invariance assumption. -/
theorem ss1FWindowRule_centered_coordinate (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (c : E) (f : E → ℝ) (G : E → E)
    (split : (Fin (n+2) → E) → Fin (n+1) → ℝ) (q : Fin (n+2) → E) :
    T (ss1FWindowRule f G split q-c)=
      ss1FWindowRule (centeredMetricObjective T c f) (centeredMetricGradient T c G)
        (centeredSplit T c split) (fun i=>T (q i-c)) := by
  have hl : centeredSplit T c split (fun i=>T (q i-c))=split q := by
    unfold centeredSplit
    congr 1
    funext i
    rw [T.symm_apply_apply]
    abel
  simp only [ss1FWindowRule,hl]
  have hp:=ss1FPoint_centered_coordinate T hT c f G
    (fun i : Fin (n+1)=>q i.castSucc) (fun i=>q i.succ-q i.castSucc) (split q) (q (Fin.last (n+1)))
  simpa only [map_sub,sub_sub_sub_cancel_right] using hp

/-- The genuine entire SS1-F trajectory obeys the actual coordinate
dictionary for every original split policy. -/
theorem ss1FSequence_centered_coordinate (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (c : E) (f : E → ℝ) (G : E → E)
    (split : (Fin (n+2) → E) → Fin (n+1) → ℝ) (seed : Fin (n+2) → E) (j : ℕ) :
    T (ss1FSequence f G split seed j-c)=
      ss1FSequence (centeredMetricObjective T c f) (centeredMetricGradient T c G)
        (centeredSplit T c split) (fun i=>T (seed i-c)) j := by
  let x:=fun k=>T (ss1FSequence f G split seed k-c)
  have hstep (k : ℕ) : x (k+n+2)=ss1FWindowRule (n:=n)
      (centeredMetricObjective T c f) (centeredMetricGradient T c G)
      (centeredSplit T c split) (fun i=>x (k+i.val)) := by
    change T (slidingSequence (ss1FWindowRule f G split) seed (k+n+2)-c)=_
    rw [slidingSequence_step]
    exact ss1FWindowRule_centered_coordinate T hT c f G split _
  have hh:=slidingSequence_shift_eq (ss1FWindowRule (centeredMetricObjective T c f)
    (centeredMetricGradient T c G) (centeredSplit T c split)) x 0 (fun k _=>hstep k) j
  have hs : (fun i : Fin (n+2)=>x (0+i.val))=(fun i=>T (seed i-c)) := by
    funext i
    dsimp only [x]
    rw [Nat.zero_add,ss1FSequence,slidingSequence_seed]
  rw [Nat.zero_add,hs] at hh
  exact hh

end
end krylov.Convergence
