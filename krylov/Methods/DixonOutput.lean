import krylov.Methods.DixonReference
import krylov.Methods.EvaluatedBFGS
import krylov.OneGradient.EvaluatedCorrection
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(b), original Dixon final corrections.
Use: retain both literal outputs: recorded CG projection and genuine BFGS
inverse action. Derive their true predicted quantities and full-cycle inverse.
Source: actual complete implementation histories, own-returned projection,
genuine BFGS secants and actual terminal CG residual, without an output substitution. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference krylov.OneGradient
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Both genuine Dixon transcripts have exactly the original true predicted
CG point and gradient from their literal observed recorded projections.
Use: distinguish the predictor from the final quasi-Newton inverse output.
Article: main_krylov, prop:classical(b), Dixon73/Dixon75 Section 3.
Proof: the proved genuine execution bridge identifies the actual complete
observations. Its real own-returned point correction is the actual virtual
solve, and the original image correction is its true predicted CG gradient. -/
theorem dixon_predicted_reference (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (k : ℕ) (hk : k≤N) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    let H := oneGradientRun method (fun _ => Q) g k
    H.displacement+recordedProjectionCorrection H=CG.displacement Q g k ∧
      recordedPredictedGradient H=CG.gradient Q g k := by
  have he := dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht k hk
  have ht' : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0 := by
    intro j hj
    rw [dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht j hj.le]
    exact (ht j hj).ne'
  dsimp only
  rw [← he]
  constructor
  · rw [evaluated_recorded_projection trial Q hQ hpos g N hpre ht' k hk]
    exact (evaluated_launch_reference trial Q hQ hpos g N hpre ht' k hk).1
  · exact evaluated_recorded_predicted_gradient trial Q hQ hpos g N hpre ht' k hk

/-- At actual CG termination, each original literal Dixon final correction
is precisely the genuine full observed-model projection correction.
Use: the BFGS inverse action remains the actual implemented output; its
terminal equality is derived from its genuine accumulated secant recursion.
Article: main_krylov, prop:classical(b).
Proof: true complete histories transfer to the real evaluated transcript.
For CG use the literal recorded projection identity. For BFGS, the proved
actual inverse action on the stored span and true CG termination identify
its genuinely different implemented final output with that same correction. -/
theorem dixon_output_at_termination (bfgs : Bool) (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => Q) g j))
    (hstop : CG.gradient Q g N=0) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    let H := oneGradientRun method (fun _ => Q) g N
    method.output H=virtualCorrection H.pairs H.gradient := by
  have he := dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht N le_rfl
  have ht' : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0 := by
    intro j hj
    rw [dixon_evaluated_histories bfgs trial Q hQ hpos g N hpre ht j hj.le]
    exact (ht j hj).ne'
  dsimp only
  cases bfgs with
  | false =>
    change oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g N=
      oneGradientRun (dixonCGMethod trial) (fun _ => Q) g N at he
    change recordedProjectionCorrection (oneGradientRun (dixonCGMethod trial) (fun _ => Q) g N)=
      virtualCorrection (oneGradientRun (dixonCGMethod trial) (fun _ => Q) g N).pairs
        (oneGradientRun (dixonCGMethod trial) (fun _ => Q) g N).gradient
    rw [← he]
    exact evaluated_recorded_projection trial Q hQ hpos g N hpre ht' N le_rfl
  | true =>
    change oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g N=
      oneGradientRun (dixonBFGSMethod trial) (fun _ => Q) g N at he
    change -inverseBFGSApply 1 (oneGradientRun (dixonBFGSMethod trial) (fun _ => Q) g N).pairs
      (oneGradientRun (dixonBFGSMethod trial) (fun _ => Q) g N).gradient=
        virtualCorrection (oneGradientRun (dixonBFGSMethod trial) (fun _ => Q) g N).pairs
          (oneGradientRun (dixonBFGSMethod trial) (fun _ => Q) g N).gradient
    rw [← he]
    exact evaluated_bfgs_terminal_correction trial Q hQ hpos g N hpre ht' hstop

end
noncomputable section
open Matrix krylov.Reference krylov.OneGradient
variable {n : ℕ}

/-- Both literal original full-cycle Dixon outputs are exactly Hestenes's
true inverse-matrix action on their own actual evaluated gradient.
Use: the classical comparison has the genuine computed BFGS model and the
real recorded CG correction, without a postulated output/model equivalence.
Article: main_krylov, prop:classical(b), Dixon73/Dixon75.
Proof: real active-atom CG termination supplies the terminal theorem. The
proved actual corrections and complete histories identify the genuine
projection executor's already proved full-cycle Hestenes inverse action. -/
theorem dixon_final_inverse_action (bfgs : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ j<n,0 < trial (oneGradientRun
      (if bfgs then dixonBFGSMethod trial else dixonCGMethod trial) (fun _ => cgOperator base) g j)) :
    let method := if bfgs then dixonBFGSMethod trial else dixonCGMethod trial
    let H := oneGradientRun method (fun _ => cgOperator base) g n
    method.output H= -cgOperator base⁻¹ H.gradient := by
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 := fun i hi => cg_nonstagnation base hb g i (by omega)
  have hstop := cg_terminates base hb g
  rw [hc] at hstop
  have he := dixon_evaluated_histories bfgs trial (cgOperator base) hp.1 hp.2 g n hpre ht n le_rfl
  have ht' : ∀ j<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g j)≠0 := by
    intro j hj
    rw [dixon_evaluated_histories bfgs trial (cgOperator base) hp.1 hp.2 g n hpre ht j hj.le]
    exact (ht j hj).ne'
  have hout := evaluated_final_inverse_action trial base hb g hc ht'
  change virtualCorrection _ _= -cgOperator base⁻¹ _ at hout
  rw [he] at hout
  dsimp only
  rw [dixon_output_at_termination bfgs trial (cgOperator base) hp.1 hp.2 g n hpre ht hstop]
  exact hout

end
end krylov.Methods
