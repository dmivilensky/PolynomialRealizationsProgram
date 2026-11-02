import krylov.Methods.DirectionWindows

/-!
Article: main_krylov, lem:consistent(c), computed direction-window solves.
Use: recover the true virtual CG point from any actual off-iterate component
in a retained direction window, without assuming a model-solve response.
Source: positive Galerkin uniqueness and the actual Fletcher--Reeves recurrence.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual conjugacy solve on any positive newest-retaining reference direction window returns the true current CG direction.
Use: full, sliding and restarted direction windows share the same computed quadratic search.
Article: main_krylov, lem:consistent(c), retaining the newest direction suffices.
Proof: Fletcher--Reeves puts the negative-gradient correction in the newest
retained direction, and genuine conjugacy and positive Gram uniqueness determine the computed solve. -/
theorem directionWindow_direction (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) (hm : 0<k → 0<m) :
    windowDirection (directionWindow Q g k m) (CG.gradient Q g k)=CG.direction Q g k := by
  -- Only the actually retained newest direction is needed in the candidate's span equation.
  let W := directionWindow Q g k m
  have hy := directionWindow_images Q g k m
  apply conjugacyDirection_unique
  · have he : windowImages W=fun i => Q (windowSteps W i) := funext hy
    rw [he]
    exact isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos
      (directionWindow_independent Q hQ hpos g k m hg)).det_pos.ne'
  · change CG.direction Q g k+CG.gradient Q g k∈pairSpan W
    cases k with
    | zero => change -g+g∈_; rw [neg_add_cancel]; exact Submodule.zero_mem _
    | succ k =>
      have he : CG.direction Q g (k+1)+CG.gradient Q g (k+1)=CG.beta Q g k • CG.direction Q g k := by
        rw [CG.direction_succ]
        abel
      rw [he]
      exact Submodule.smul_mem _ _ (directionWindow_newest Q g (Nat.succ_pos _) (hm (Nat.succ_pos _)))
  · ext i
    change inner ℝ (windowImages W i) (CG.direction Q g k)=0
    rw [hy]
    have he := hQ (windowSteps W i) (CG.direction Q g k)
    change inner ℝ (Q (windowSteps W i)) (CG.direction Q g k)=
      inner ℝ (windowSteps W i) (Q (CG.direction Q g k)) at he
    rw [he]
    exact directionFlag_conjugate Q hQ hpos g k hg (directionWindow_mem_flag Q g k m i)

/-- The computed direction-window virtual solve removes every actual retained-span off-iterate component and returns the true CG residual and direction.
Use: the actual XRFC-D execution induction needs only its physical off-iterate invariant and observed direction pairs.
Article: main_krylov, lem:consistent(c), virtual reference identities.
Proof: the negative off-iterate component lies in the real retained span and
its corrected residual is the true Galerkin residual; computed positive-model uniqueness and the actual direction solve apply. -/
theorem directionWindow_virtual (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : ∀ i<k, CG.gradient Q g i≠0) (hm : 0<k → 0<m)
    (v : E) (hv : v∈pairSpan (directionWindow Q g k m)) :
    let W := directionWindow Q g k m
    virtualCorrection W (CG.gradient Q g k+Q v)= -v ∧
      virtualGradient W (CG.gradient Q g k+Q v)=CG.gradient Q g k ∧
      windowDirection W (virtualGradient W (CG.gradient Q g k+Q v))=CG.direction Q g k := by
  -- The actual finite inverse is identified by its normal equations on the retained physical family.
  let W := directionWindow Q g k m
  have he : CG.gradient Q g k+Q v+Q (-v)=CG.gradient Q g k := by
    rw [map_neg, add_neg_cancel_right]
  have hc := virtualCorrection_unique W Q hQ hpos (directionWindow_images Q g k m)
    (directionWindow_independent Q hQ hpos g k m hg) (CG.gradient Q g k+Q v) (-v)
    (Submodule.neg_mem _ hv) (by
      rw [he]
      ext i
      exact directionFlag_gradient_orthogonal Q hQ hpos g k hg (directionWindow_mem_flag Q g k m i))
  have hgrad : virtualGradient W (CG.gradient Q g k+Q v)=CG.gradient Q g k := by
    rw [virtualGradient_quadratic W Q _ (directionWindow_images Q g k m), hc, he]
  exact ⟨hc,hgrad,by rw [hgrad]; exact directionWindow_direction Q hQ hpos g k m hg hm⟩

end
end krylov.Methods
