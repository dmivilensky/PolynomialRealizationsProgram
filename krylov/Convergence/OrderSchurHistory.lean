import krylov.Convergence.OrderHistoryScale
import krylov.Convergence.OrderSchurScale
import krylov.Cancellation.DCSchurEstimate
import krylov.Cancellation.DCSlide
import krylov.Methods.DeferredReindex

/-!
Article: main_krylov, thm:D and s8:dcsdef, literal DC observed-estimate homogeneity.
Use: discharge positive homogeneity for the actual data-based Schur
arithmetic midpoint policy, on every genuine supplied observed history.
Source: exact stored-gradient/secant scaling, actual finite inverse solves
and the proved common-scale covariance of the literal Schur formula.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Cancellation krylov.Completion
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The concrete Schur arithmetic estimate has degree zero in every real
observed history, including singular totalized data. Article: thm:D, DC. -/
theorem dcSchurGaussRadauEstimate_history_scale
    (memory : ℕ → ℕ) (mu upper c : ℝ) (hc : c≠0) (H : History E) :
    dcSchurGaussRadauEstimate memory mu upper (scaleHistory c H)=
      dcSchurGaussRadauEstimate memory mu upper H := by
  let W:=selectedWindow memory H
  let V:=orderScalePairs c W
  let s:=fun i : Fin W.length=>(W.getD i.val (0,0)).1
  let y:=fun i : Fin W.length=>(W.getD i.val (0,0)).2
  let g:=H.gradient
  let d:=windowDirection W g
  have hlen : V.length=W.length := List.length_map _
  have hd : windowDirection V (c • g)=c • d := orderScalePairs_direction c hc W g
  have hv : virtualGradient V (c • g)=c • virtualGradient W g := orderScalePairs_virtualGradient c hc W g
  have hq : dcCurvatureSlope memory (scaleHistory c H)=(c*c)*dcCurvatureSlope memory H := by
    rw [dcCurvatureSlope,orderScaleHistory_selected,scaleHistory_gradient]
    change -inner ℝ (virtualGradient V (c • g)) (windowDirection V (c • g))=_
    rw [hv,hd,real_inner_smul_left,real_inner_smul_right]
    dsimp only [dcCurvatureSlope,W,g,d]
    ring
  let F : List (E × E) → E → ℝ → ℝ:=fun W g q=>
    schurArithmeticEstimate (fun a j=>windowSteps W j a)
      (fun a=>windowDirection W g a) (windowModel W) mu upper q
  change F (selectedWindow memory (scaleHistory c H)) (scaleHistory c H).gradient
    (dcCurvatureSlope memory (scaleHistory c H))=F W g (dcCurvatureSlope memory H)
  rw [orderScaleHistory_selected,scaleHistory_gradient,hq]
  change schurArithmeticEstimate (fun a j=>windowSteps V j a)
    (fun a=>windowDirection V (c • g) a) (windowModel V) mu upper
      ((c*c)*dcCurvatureSlope memory H)=
    schurArithmeticEstimate (fun a j=>windowSteps W j a)
      (fun a=>d a) (windowModel W) mu upper (dcCurvatureSlope memory H)
  rw [schur_window_coordinates V W.length hlen,schur_window_coordinates W W.length rfl,hd]
  simp only [V,orderScalePairs_getD]
  change schurArithmeticEstimate (c • (fun a j=>s j a)) (c • (fun a=>d a))
    (pairModel (fun i=>c • s i) (fun i=>c • y i)) mu upper ((c*c)*dcCurvatureSlope memory H)=_
  rw [pairModel_scalar]
  exact schurArithmeticEstimate_common_scale _ _ _ mu upper _ c hc

/-- A primitive degree-zero actual estimate gives a homogeneous full
original deferred method, including every off-domain supplied history.
Article: main_krylov, thm:D, genuine policy membership. -/
theorem deferredDataMethod_estimate_homogeneous
    (memory : ℕ → ℕ) (N : ℕ) (estimate : History E → ℝ)
    (hscale : ∀ c : ℝ,0<c →∀ H,estimate (scaleHistory c H)=estimate H) :
    (deferredDataMethod memory N estimate).Homogeneous := by
  intro c hc H
  have hlen : (scaleHistory c H).records.length=H.records.length := List.length_map _
  refine ⟨?_,fun _=>rfl⟩
  simp only [deferredDataMethod,hlen]
  split_ifs
  · let F : List (E × E) → E → ℝ → E:=fun W g a=>
      deferredDirection (windowSteps W) (windowImages W) g a
    change F (selectedWindow memory (scaleHistory c H)) (scaleHistory c H).gradient
      (estimate (scaleHistory c H))=c • F (selectedWindow memory H) H.gradient (estimate H)
    rw [orderScaleHistory_selected,scaleHistory_gradient,hscale c hc H]
    let W:=selectedWindow memory H
    change deferredDirection (windowSteps (orderScalePairs c W)) (windowImages (orderScalePairs c W))
      (c • H.gradient) (estimate H)=c • deferredDirection (windowSteps W) (windowImages W) H.gradient (estimate H)
    have hW : (orderScalePairs c W).length=W.length := List.length_map _
    rw [deferredDirection_getD_array _ W.length hW,deferredDirection_getD_array W W.length rfl]
    simp only [orderScalePairs_getD]
    exact orderDeferredDirection_scalar _ _ _ _ c hc.ne'
  · change windowDirection (selectedWindow memory (scaleHistory c H)) (scaleHistory c H).gradient=
      c • windowDirection (selectedWindow memory H) H.gradient
    rw [orderScaleHistory_selected,scaleHistory_gradient]
    exact orderScalePairs_direction c hc.ne' _ _

/-- The literal implemented data-midpoint Schur DC policy is homogeneous;
no independent trajectory or source scaling premise remains.
Article: main_krylov, thm:D, data-based midpoint estimate. -/
theorem deferredSchurMethod_homogeneous (memory : ℕ → ℕ) (N : ℕ) (mu upper : ℝ) :
    (deferredDataMethod memory N (dcSchurGaussRadauEstimate (n := n) memory mu upper)).Homogeneous :=
  deferredDataMethod_estimate_homogeneous memory N _
    (fun c hc H=>dcSchurGaussRadauEstimate_history_scale memory mu upper c hc.ne' H)

end
end krylov.Convergence
