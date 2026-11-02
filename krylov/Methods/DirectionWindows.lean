import krylov.Methods.VirtualReference
import krylov.Methods.ExecutedFC

/-!
Article: main_krylov, lem:consistent(c), retained true direction windows.
Use: compute actual quadratic model solves in any newest-retaining direction
window, for the later actual XRFC-D execution invariant.
Source: actual CG conjugacy and the newest-direction Fletcher--Reeves identity.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
/-- An actual chronological executed-pair transcript has the stated newest-first age formula.
Use: obtain concrete retained direction indices from the actual list representation.
Article: main_krylov, lem:consistent(c), newest direction retention.
Proof: induction removes the head and shifts the age of every older recorded pair. -/
theorem executedPairs_get (s y : ℕ → E) (k i : ℕ) (hi : i<k) :
    (executedPairs s y k)[i]'(by rw [executedPairs_length]; exact hi)=(s (k-1-i),y (k-1-i)) := by
  -- Every stored age refers to the actual corresponding chronological query.
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp only [executedPairs, List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero]
    | succ i =>
      simpa only [executedPairs, List.getElem_cons_succ, Nat.add_sub_cancel,
        show k-(i+1)=k-1-i by omega] using ih i (by omega)

/-- The true quadratic direction pair window retained at iteration k.
Use: the actual XRFC-D replay transcript is proved equal to this computed reference list.
Article: main_krylov, lem:consistent(c), D and Q. -/
def directionWindow (Q : E →L[ℝ] E) (g : E) (k m : ℕ) : List (E × E) :=
  (executedPairs (CG.direction Q g) (fun i => Q (CG.direction Q g i)) k).take m

/-- Every actual reference direction window entry has its true chronological direction and quadratic image.
Use: model positivity and conjugacy use actual list entries.
Article: main_krylov, lem:consistent(c), q_j=Ad_j⁰.
Proof: taking a prefix preserves the proved chronological age formula. -/
theorem directionWindow_pair (Q : E →L[ℝ] E) (g : E) (k m : ℕ) (i : Fin (directionWindow Q g k m).length) :
    (directionWindow Q g k m).get i=(CG.direction Q g (k-1-i.val),Q (CG.direction Q g (k-1-i.val))) := by
  have hi : i.val<k := by
    have h := i.isLt
    simp only [directionWindow, List.length_take, executedPairs_length] at h
    omega
  change ((executedPairs (CG.direction Q g) (fun j => Q (CG.direction Q g j)) k).take m)[i.val]=_
  rw [List.getElem_take]
  exact executedPairs_get (CG.direction Q g) (fun j => Q (CG.direction Q g j)) k i.val hi

/-- Every true retained direction lies in the actual old CG flag.
Use: the current true residual annihilates every actual retained direction.
Article: main_krylov, lem:consistent(c), old direction window.
Proof: each stored age gives an actual direction index strictly before k. -/
theorem directionWindow_mem_flag (Q : E →L[ℝ] E) (g : E) (k m : ℕ) (i : Fin (directionWindow Q g k m).length) :
    windowSteps (directionWindow Q g k m) i∈directionFlag Q g k := by
  have hi : i.val<k := by
    have h := i.isLt
    simp only [directionWindow, List.length_take, executedPairs_length] at h
    omega
  rw [show windowSteps (directionWindow Q g k m) i=CG.direction Q g (k-1-i.val) from
    congrArg Prod.fst (directionWindow_pair Q g k m i)]
  exact Submodule.subset_span ⟨k-1-i.val,by change k-1-i.val<k; omega,rfl⟩

/-- True retained direction windows are independent on every actual nonstagnating prefix.
Use: the actual direction-basis virtual and conjugacy model inverses are genuine.
Article: main_krylov, lem:consistent(c), positive diagonal DᵀAD.
Proof: the actual directions are nonzero and mutually conjugate; their
chronological index map is injective, so positive conjugate independence applies. -/
theorem directionWindow_independent (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) : LinearIndependent ℝ (windowSteps (directionWindow Q g k m)) := by
  -- All nonzero and cross-pairing properties come from the true executed reference invariant.
  let W := directionWindow Q g k m
  let idx := fun i : Fin W.length => k-1-i.val
  have hi (i : Fin W.length) : i.val<k := by
    have h := i.isLt
    simp only [W, directionWindow, List.length_take, executedPairs_length] at h
    omega
  have hr (i : Fin W.length) : idx i<k := by dsimp only [idx]; have := hi i; omega
  have hs : windowSteps W=fun i => CG.direction Q g (idx i) :=
    funext fun i => congrArg Prod.fst (directionWindow_pair Q g k m i)
  rw [hs]
  apply conjugate_independent Q hpos
  · intro i
    exact (CG.invariant_line_pos Q hpos g (idx i)
      (CG.invariant Q hQ hpos g (idx i) (fun j hj => hg j (hj.trans (hr i)))) (hg _ (hr i))).1
  · intro i j hij
    have hij' : idx i≠idx j := by
      intro he
      apply hij
      apply Fin.ext
      have := hi i
      have := hi j
      change k-1-i.val=k-1-j.val at he
      omega
    have hk := CG.invariant Q hQ hpos g k hg
    rcases lt_or_gt_of_ne hij' with h | h
    · exact hk.conjugate _ _ h (hr j).le
    · have he := hQ (CG.direction Q g (idx i)) (CG.direction Q g (idx j))
      change inner ℝ (Q (CG.direction Q g (idx i))) (CG.direction Q g (idx j))=
        inner ℝ (CG.direction Q g (idx i)) (Q (CG.direction Q g (idx j))) at he
      rw [← he, real_inner_comm]
      exact hk.conjugate _ _ h (hr i).le

/-- Every true retained direction image is its actual quadratic operator image.
Use: the genuine latest model equals the actual operator Gram matrix.
Article: main_krylov, lem:consistent(c), Q=AD.
Proof: both components of the actual direction pair have their proved age description. -/
theorem directionWindow_images (Q : E →L[ℝ] E) (g : E) (k m : ℕ) (i : Fin (directionWindow Q g k m).length) :
    windowImages (directionWindow Q g k m) i=Q (windowSteps (directionWindow Q g k m) i) := by
  change ((directionWindow Q g k m).get i).2=Q ((directionWindow Q g k m).get i).1
  rw [directionWindow_pair]

/-- A positive newest-retaining direction window contains the actual immediately preceding reference direction.
Use: every true off-iterate component in XRFC-D is removable in its real retained span.
Article: main_krylov, lem:consistent(c), retain newest pair.
Proof: the real index zero entry has actual chronological time k−1. -/
theorem directionWindow_newest (Q : E →L[ℝ] E) (g : E) {k m : ℕ} (hk : 0<k) (hm : 0<m) :
    CG.direction Q g (k-1)∈pairSpan (directionWindow Q g k m) := by
  -- Positive retention makes the actual newest age-zero entry available.
  have hl : 0<(directionWindow Q g k m).length := by
    simp only [directionWindow, List.length_take, executedPairs_length]
    omega
  have hp := congrArg Prod.fst (directionWindow_pair Q g k m ⟨0,hl⟩)
  change windowSteps (directionWindow Q g k m) ⟨0,hl⟩=CG.direction Q g (k-1-0) at hp
  have he : windowSteps (directionWindow Q g k m) ⟨0,hl⟩=CG.direction Q g (k-1) := by
    simpa only [Nat.sub_zero] using hp
  rw [← he]
  exact Submodule.subset_span ⟨⟨0,hl⟩,rfl⟩

end
end krylov.Methods
