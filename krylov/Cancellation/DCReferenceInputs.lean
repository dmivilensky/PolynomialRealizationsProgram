import krylov.Cancellation.DCPhysicalWindow
import krylov.Methods.ReferenceModels
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs and s8:dcsdef, true exact-search DC inputs.
Use: derive actual independent quadratic windows, proper-flag membership
and strictly positive original observed descent pairing for every native
exact-search DC estimate policy and positive newest-retaining memory.
Source: genuine DC/FC complete-history equality and true CG orthogonality.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine exact-search DC execution supplies every native input
domain needed by observed arithmetic/harmonic curvature policies.
Use: no positivity or smoothness of the estimate is required to establish
its own true quadratic reference domains.
Article: main_krylov, thm:dcs(b,c) and s8:dcsdef.
Proof: actual DC and FC complete histories agree. Genuine CG observations
give the independent retained pair window and its proper-flag membership.
The actual virtual correction has zero right-hand side, while the untilted
direction is the true CG direction; its real descent pairing is positive. -/
theorem dc_reference_inputs (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) :
    let H := methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k
    let W := selectedWindow memory H
    LinearIndependent ℝ (windowSteps W) ∧
      (∀ i,windowImages W i=Q (windowSteps W i)) ∧
      (∀ i,windowSteps W i∈directionFlag Q g k) ∧ 0<dcCurvatureSlope memory H := by
  let H := methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k
  let W := selectedWindow memory H
  have hrun := dc_slide_reference_run memory hm estimate Q hQ hpos g k
  have hfc := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
  have hp : H.pairs=referencePairs Q g k := (congrArg History.pairs hrun).trans hfc.2
  have hg : H.gradient=CG.gradient Q g k := (congrArg History.gradient hrun).trans hfc.1
  have hW : W=(referencePairs Q g k).take (memory k) := by
    unfold W selectedWindow
    rw [hp,methodRun_length]
  have hLI : LinearIndependent ℝ (windowSteps W) := by
    rw [hW]
    exact retainedSteps_independent Q hQ hpos g k (memory k) (fun i hi => hpre i (by omega))
  have hy : ∀ i,windowImages W i=Q (windowSteps W i) := by
    rw [hW]
    exact retainedImages_quadratic Q g k (memory k)
  have hflag : ∀ i,windowSteps W i∈directionFlag Q g k := by
    rw [hW]
    intro i
    have hi : i.val<k := by
      have h := i.isLt
      simp only [List.length_take,referencePairs_length] at h
      omega
    have he := congrArg Prod.fst (retained_pair Q g k (memory k) i)
    change windowSteps _ i∈_
    rw [show windowSteps ((referencePairs Q g k).take (memory k)) i=referenceStep Q g (k-1-i.val) from he]
    change (CG.length Q g (k-1-i.val)) • CG.direction Q g (k-1-i.val)∈_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k-1-i.val,by change k-1-i.val<k;omega,rfl⟩)
  have hv : virtualGradient W H.gradient=CG.gradient Q g k := by
    have hc := history_reference_coordinates_zero Q hQ hpos g k H hp hg memory
    unfold virtualGradient virtualCoefficients
    rw [modelCoefficients_zero _ _ _ hc]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero,hg]
  have hd : windowDirection W H.gradient=CG.direction Q g k := by
    rw [hW,hg]
    exact windowDirection_reference Q hQ hpos g k (memory k) (hpre k (by omega)) (hm k)
  have hpair : inner ℝ (CG.gradient Q g k) (CG.direction Q g k)= -‖CG.gradient Q g k‖^2 := by
    rw [real_inner_comm]
    exact (CG.invariant Q hQ hpos g k (fun i hi => hpre i (by omega))).search_pair
  refine ⟨hLI,hy,hflag,?_⟩
  change 0 < -inner ℝ (virtualGradient W H.gradient) (windowDirection W H.gradient)
  rw [hv,hd,hpair,neg_neg]
  exact sq_pos_of_pos (norm_pos_iff.mpr (hpre k (by omega)))

end
end krylov.Cancellation
