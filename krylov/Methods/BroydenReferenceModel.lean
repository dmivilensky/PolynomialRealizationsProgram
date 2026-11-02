import krylov.Methods.BroydenModel
import krylov.Methods.BroydenConvexScale
import krylov.Methods.LBFGSReference

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine full convex Broyden reference-model induction.
Use: derive true positive CG direction scaling and actual untouched future-gradient actions for the real accumulated observed-pair inverse model.
Source: proved actual endpoint pair actions, genuine convex-scale positivity and real finite CG gradient/direction orthogonality.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On every true active CG prefix the genuine accumulated convex Broyden model has a positive actual current direction scale and preserves the real scalar action on all future reference gradients.
Use: On every true active CG prefix the genuine accumulated convex Broyden model has a positive actual current direction scale and preserves the real scalar action on all future reference gradients.
Article: main_krylov, def:classes, genuine full convex Broyden reference-model induction.
Proof: Induct through actual newest-first CG pairs; the genuine current update uses its proved positive scale and all true future pairings vanish by actual CG orthogonality. -/
theorem inverseBroydenModel_reference_prefix (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q g i≠0) (k : ℕ) (hk : k≤N) :
    let H := inverseBroydenModel c θ (referencePairs Q g k)
    ∃ a : ℝ,0<a ∧ H (CG.gradient Q g k)= -a • CG.direction Q g k ∧
      ∀ j : ℕ,k<j → j≤N → H (CG.gradient Q g j)=c • CG.gradient Q g j := by
  -- Strengthen the actual reference invariant with every genuine future-gradient action before adding the next real pair.
  induction k with
  | zero =>
    refine ⟨c,hc,?_,fun _ _ _ => rfl⟩
    simp only [referencePairs,inverseBroydenModel,LinearMap.smul_apply,LinearMap.id_apply]
    change c • g= -c • (-g)
    simp only [smul_neg,neg_smul,neg_neg]
  | succ k ih =>
    obtain ⟨a,ha,hg,hfuture⟩ := ih (by omega)
    let H := inverseBroydenModel c θ (referencePairs Q g k)
    let d := CG.direction Q g k
    let r := CG.gradient Q g (k+1)
    have hkN : k<N := by omega
    have hIk := CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans hkN))
    have hIn := CG.invariant Q hQ hpos g (k+1) (fun i hi => hpre i (by omega))
    have hα : CG.length Q g k≠0 := (CG.invariant_line_pos Q hpos g k hIk (hpre k hkN)).2.1.ne'
    have hgd : inner ℝ (CG.gradient Q g k) d= -‖CG.gradient Q g k‖^2 := by
      rw [real_inner_comm]
      exact hIk.search_pair
    have hrd : inner ℝ r d=0 := by rw [real_inner_comm];exact hIn.old_direction k (by omega)
    have hgr : inner ℝ (CG.gradient Q g k) r=0 := hIn.old_gradient k (by omega)
    have hr : H r=c • r := hfuture (k+1) (by omega) hk
    -- The genuine current secant update has a true positive next-CG scale, including the real interpolation endpoints.
    obtain ⟨b,hb,hnew⟩ := inverseBroydenUpdate_reference H (CG.gradient Q g k) r d c a
      (CG.length Q g k) (θ k) hc ha hα (hpre k hkN) (hθ k) hg hr hgd hrd hgr
    have hmodel : inverseBroydenModel c θ (referencePairs Q g (k+1))=
        inverseBroydenUpdate H (CG.length Q g k • d) (r-CG.gradient Q g k) (θ k) := by
      rw [referencePairs,inverseBroydenModel,referencePairs_length]
      have hy : Q (referenceStep Q g k)=r-CG.gradient Q g k := by
        rw [referenceStep,map_smul]
        exact (CG.gradient_change Q g k).symm
      rw [hy]
      rfl
    refine ⟨b,hb,?_,?_⟩
    · rw [hmodel]
      change inverseBroydenUpdate H (CG.length Q g k • d) (r-CG.gradient Q g k) (θ k) r=_
      rw [hnew,CG.direction_succ]
    -- Actual later gradients are perpendicular to both real pair vectors, so both genuine endpoint updates preserve their scalar action.
    · intro j hkj hjN
      rw [hmodel]
      apply inverseBroydenUpdate_future
      · exact hfuture j (by omega) hjN
      · have hIj := CG.invariant Q hQ hpos g j (fun i hi => hpre i (hi.trans_le hjN))
        rw [real_inner_smul_left,hIj.old_direction k (by omega),mul_zero]
      · have hIj := CG.invariant Q hQ hpos g j (fun i hi => hpre i (hi.trans_le hjN))
        rw [inner_sub_left,hIj.old_gradient (k+1) hkj,hIj.old_gradient k (by omega),sub_self]
end
end krylov.Methods
