import krylov.Methods.NazarethEvaluated
import krylov.OneGradient.RecordedProjection
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a,b), complete original Nazareth projection.
Use: connect the literal measured final correction and actual evaluated
transcript to the true predicted CG output and Hestenes final inverse action.
Source: genuine Nazareth/evaluated history equality and exact own-returned
record projection dictionary; the real output spends no further query. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference krylov.OneGradient
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal original Nazareth final correction is exactly the genuine
full observed-model projection on its actual quadratic complete history.
Use: the real own-newly-returned-gradient output, not a substitute correction,
gives the original predicted point and gradient.
Article: main_krylov, prop:classical(b), Nazareth77 equation (16).
Proof: the actual complete transcript equals the genuine evaluated-launch
transcript at its derived positive effective trials; the already proved
recorded-gradient projection identity identifies the actual final correction. -/
theorem nazareth_output_reference (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (nazarethMethod trial) (fun _ => Q) g k
    (nazarethMethod trial).output H=virtualCorrection H.pairs H.gradient := by
  have he := nazareth_evaluated_histories trial Q hQ hpos g N hpre ht k hk
  change recordedProjectionCorrection _=virtualCorrection _ _
  rw [← he]
  exact evaluated_recorded_projection (nazarethEvaluatedTrial trial) Q hQ hpos g N hpre
    (fun j hj => (nazareth_evaluated_trials_positive trial Q hQ hpos g N hpre ht j hj).ne') k hk

/-- The genuine original Nazareth final predicted point is exactly the
true CG iterate on every active quadratic prefix.
Use: the named classical implementation has the source predicted-output
identity derived from its literal measured recurrence and final correction.
Article: main_krylov, prop:classical(a,b).
Proof: the actual output equals its genuine observed-model projection,
whose true predicted displacement was derived from the real stored basis. -/
theorem nazareth_output_displacement (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    (nazarethMethod trial).outputDisplacement (oneGradientRun (nazarethMethod trial) (fun _ => Q) g k)=
      CG.displacement Q g k := by
  rw [OneGradientMethod.outputDisplacement,nazareth_output_reference trial Q hQ hpos g N hpre ht k hk,
    (nazareth_predicted_reference trial Q hQ hpos g N hpre ht k hk).1,add_sub_cancel]

end
noncomputable section
open Matrix krylov.Reference krylov.OneGradient
variable {n : ℕ}

/-- The genuine original full-cycle Nazareth correction is precisely the
Hestenes inverse action on its actual evaluated gradient.
Use: the original named algorithm uses n+one observed gradients and its
literal recorded final projection gives the true matrix inverse action.
Article: main_krylov, prop:classical(b).
Proof: genuine complete histories and the actual recorded-projection output
coincide with the real evaluated-launch method at its derived positive
lengths. Transfer its already proved true full-cycle inverse action. -/
theorem nazareth_final_inverse_action
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,0 < trial (oneGradientRun (nazarethMethod trial) (fun _ => cgOperator base) g i)) :
    let H := oneGradientRun (nazarethMethod trial) (fun _ => cgOperator base) g n
    (nazarethMethod trial).output H= -cgOperator base⁻¹ H.gradient := by
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by omega)
  have he := nazareth_evaluated_histories trial (cgOperator base) hp.1 hp.2 g n hpre ht n le_rfl
  have hout := evaluated_final_inverse_action (nazarethEvaluatedTrial trial) base hb g hc
    (fun i hi => (nazareth_evaluated_trials_positive trial (cgOperator base) hp.1 hp.2 g n hpre ht i hi).ne')
  change _=_ at hout
  rw [he] at hout
  dsimp only
  rw [nazareth_output_reference trial (cgOperator base) hp.1 hp.2 g n hpre ht n le_rfl]
  exact hout

end
end krylov.Methods
