import krylov.Cancellation.DCPhysicalWindow
import krylov.Cancellation.DCLinearizedResidual
import krylov.Cancellation.ResidualGeometric
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), actual arithmetic reference damping.
Use: derive the source spectral contraction factor for the real searched
length and original observed Gauss--Radau estimate on genuine DC histories.
Source: exact full quadratic DC/FC history, native Galerkin/conjugacy solves
and true physical matrix-completion damping with all source domains derived.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Completion
open scoped BigOperators
variable {n : ℕ}

/-- The actual exact-search arithmetic DC reference multiplier has the
original class-wide spectral contraction factor for every positive memory.
Use: no independent exact length, scalar interval, feasible completion,
window rank or assumed native descent pairing enters this source estimate.
Article: main_krylov, thm:dcs(c), genuine |epsilonHat^0|≤rho_kappa.
Proof: real quadratic history equality gives the genuine CG residual and
retained pairs. Their zero old residual makes the true virtual gradient the
actual CG gradient and removes the real tilt. Positive native CG descent,
actual retained independence and genuine quadratic images discharge every
physical completion domain. The original matrix scenario then gives the
proved arithmetic damping bound for precisely the real searched length. -/
theorem dc_gauss_radau_reference_damping
    (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hgrad : CG.gradient (cgOperator base) g k≠0) :
    let Q := cgOperator base
    let estimate := dcGaussRadauEstimate memory mu L (n := n)
    let H := methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k
    0<estimate H ∧
      |1-dcSearchedLength memory estimate (fun _ => Q) (fun _ => Q) g k/estimate H|≤(L-mu)/(L+mu) := by
  let Q := cgOperator base
  let estimate := dcGaussRadauEstimate memory mu L (n := n)
  let m := dcSlideMethod memory estimate
  let H := methodRun m (fun _ => Q) (fun _ => Q) g k
  let W := selectedWindow memory H
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  have hstatic : H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k := by
    dsimp only [H,m]
    rw [dc_slide_reference_run memory hm estimate Q hQ hpos g k]
    exact fcMethod_static memory Q hQ hpos g (fun j _ => hm j) k
  have hpre : ∀ j<k,CG.gradient Q g j≠0 := by
    intro j hj hz
    exact hgrad (CG.gradient_eq_zero_of_le Q g hz hj.le)
  have hW : W=(referencePairs Q g k).take (memory k) := by
    change H.pairs.take (memory H.records.length)=_
    rw [show H.records.length=k from methodRun_length _ _ _ _ _,hstatic.2]
  have hd : windowDirection W H.gradient=CG.direction Q g k :=
    retainedMethod_direction memory (fun _ _ => .done) Q hQ hpos g k H hstatic.1 hstatic.2 (fun _ => hm k)
  have hc := history_reference_coordinates_zero Q hQ hpos g k H hstatic.2 hstatic.1 memory
  have hw : virtualCoefficients W H.gradient=0 := modelCoefficients_zero _ _ _ hc
  have hv : virtualGradient W H.gradient=CG.gradient Q g k := by
    rw [virtualGradient,hw]
    simpa only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero] using hstatic.1
  have hInv := CG.invariant Q hQ hpos g k hpre
  have hslope : dcCurvatureSlope memory H=‖CG.gradient Q g k‖^2 := by
    change -inner ℝ (virtualGradient W H.gradient) (windowDirection W H.gradient)=_
    rw [hv,hd]
    have hp : inner ℝ (CG.gradient Q g k) (CG.direction Q g k)= -‖CG.gradient Q g k‖^2 :=
      (real_inner_comm _ _).trans hInv.search_pair
    rw [hp,neg_neg]
  have hq : 0<dcCurvatureSlope memory H := by rw [hslope];exact sq_pos_of_pos (norm_pos_iff.mpr hgrad)
  have hY : ∀ j,windowImages W j=Q (windowSteps W j) := by
    rw [hW]
    exact retainedImages_quadratic Q g k (memory k)
  have hLI : LinearIndependent ℝ (windowSteps W) := by
    rw [hW]
    exact retainedSteps_independent Q hQ hpos g k (memory k) hpre
  have hbound := dc_quadratic_gauss_radau_bound memory H base hb mu L hmu hmuL hlo hhi hY hLI hq
  have hbase := (dc_quadratic_window_feasible memory H base hb mu L hlo hhi hY hLI hq).2.2
  have hdM : m.direction H=CG.direction Q g k :=
    (dc_slide_reference_direction memory estimate Q hQ hpos g k H hstatic.2 hstatic.1).trans hd
  have hraw : dcObservedUntilted memory H=(CG.direction Q g k).ofLp := by
    funext j
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) hd
  have hsearch : dcSearchedLength memory estimate (fun _ => Q) (fun _ => Q) g k=
      physicalTrialLength (dcObservedUntilted memory H) (dcCurvatureSlope memory H) base := by
    change lineLength H.gradient (m.direction H) (Q (m.direction H))=_
    rw [hstatic.1,hdM,physicalTrialLength,hraw,hslope]
    unfold lineLength
    rw [hInv.search_pair,neg_neg]
    congr 1
    exact Matrix.inner_toEuclideanCLM _ _ _
  refine ⟨hbound.1,?_⟩
  rw [hsearch]
  exact hbound.2 base hbase

end
end krylov.Cancellation
