import krylov.Cancellation.DCSchurNative
import krylov.Cancellation.DCOneGradientRegularity
import krylov.Stability.OneGradientTrialBridge
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef and lem:U(d), complete native Schur execution regularity.
Use: prove actual exact-search and one-gradient DC returned-gradient/step
regularity for the literal interval-rule continuation, with all primitive
estimate hypotheses discharged from genuine physical reference data.
Source: actual native Schur estimate domains, exact full-history/trial-chart
bridge and the existing real query execution calculus.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual one-gradient Schur arithmetic estimate has precisely the
native primitive trial-coordinate C-r regularity at every true active reference.
Use: the one-gradient query calculus receives a proved trial hypothesis.
Article: main_krylov, s8:dcsdef and lem:U(d).
Proof: native execution supplies the genuine full observed-history scalar
chart; the actual one-gradient history dictionary and proved chart bridge
transfer it to exactly the original trial coordinates. -/
theorem dc_schur_one_gradient_trial_regular
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ j<N,CG.gradient (cgOperator base) g j≠0)
    (r : WithTop ℕ∞) (k : ℕ) (hk : k<N) :
    let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
    let method := dcSlideOneGradient fullMemory estimate
    ContDiffAt ℝ r (trialCoordinate estimate k) (oneGradientData method (fun _ => cgOperator base) g k) := by
  let estimate := dcSchurGaussRadauEstimate fullMemory mu upper (n := n)
  let method := dcSlideOneGradient fullMemory estimate
  have h := (dc_schur_one_gradient_estimates base hb mu upper hmu hmuL hlo hhi g N hpre r k hk).2
  have he := oneGradientRun_chart method (fun _ => cgOperator base) g k
  change oneGradientRun method (fun _ => cgOperator base) g k=
    oneGradientHistoryChart (oneGradientData method (fun _ => cgOperator base) g k) at he
  change ContDiffAt ℝ r (historyEstimateChart estimate
    (oneGradientRun method (fun _ => cgOperator base) g k).queryShape
    (oneGradientRun method (fun _ => cgOperator base) g k).observationList.length)
      (observedArray (oneGradientRun method (fun _ => cgOperator base) g k).observationList.length
        (oneGradientRun method (fun _ => cgOperator base) g k).observationList) at h
  rw [he] at h
  exact trialCoordinate_of_history_estimate estimate _ h

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The literal full-memory one-gradient arithmetic Schur DC executor has
all actual queried steps and returned gradients C-r from primitive smooth
operators and initial observations at every true physical-band reference.
Use: no smooth chosen estimate, trajectory or inverse domain is assumed;
the complete original finite query regularity is proved for this implementation.
Article: main_krylov, s8:dcsdef, thm:dcs and lem:U(d).
Proof: actual native positive estimates and the derived original trial-coordinate
charts discharge both scalar hypotheses of the existing genuine DC query
induction; its actual independent quadratic flag supplies every model inverse. -/
theorem dc_schur_one_gradient_contDiffAt {r : WithTop ℕ∞}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : X → EuclideanSpace ℝ (Fin n)) (x : X)
    (hA : ∀ i,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (hAx : A x=fun _ => cgOperator base) (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) (g x) i≠0) :
    let method := dcSlideOneGradient fullMemory (dcSchurGaussRadauEstimate fullMemory mu upper (n := n))
    (∀ k≤N,ContDiffAt ℝ r (fun z => oneGradientGradient method (A z) (g z) k) x) ∧
      ∀ i<N,ContDiffAt ℝ r (fun z => oneGradientStep method (A z) (g z) i) x := by
  have hp := cgOperator_positive base hb
  apply quadraticDC_one_gradient_contDiffAt (dcSchurGaussRadauEstimate fullMemory mu upper)
    A g x hA hg (cgOperator base) hAx hp.1 hp.2 N hpre
  · exact fun k hk => (dc_schur_one_gradient_estimates base hb mu upper hmu hmuL hlo hhi (g x) N hpre r k hk).1
  · intro k hk
    rw [hAx]
    exact dc_schur_one_gradient_trial_regular base hb mu upper hmu hmuL hlo hhi (g x) N hpre r k hk

/-- The literal newest-retaining exact-search Schur DC executor has its
genuine returned-gradient C-r regularity under primitive varying operators.
Use: the actual smooth source cycle and every positive estimate condition
are derived for the implementation, with no extra smooth-estimate premise.
Article: main_krylov, s8:dcsdef, thm:dcs(c) and lem:U(d).
Proof: the actual native Schur source-cycle theorem supplies the real primitive
coefficient representation; genuine CG consistency and the original smooth
query calculus give regularity of the same actual returned-gradient cycle. -/
theorem dc_schur_slide_gradient_contDiffAt {r : WithTop ℕ∞}
    (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : X → EuclideanSpace ℝ (Fin n)) (x : X) (N : ℕ)
    (hA : ∀ i<N,ContDiffAt ℝ r (fun z => A z i) x)
    (hB : ∀ i<N,ContDiffAt ℝ r (fun z => B z i) x) (hg : ContDiffAt ℝ r g x)
    (hAx : A x=fun _ => cgOperator base) (hBx : B x=fun _ => cgOperator base)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) (g x) i≠0) :
    let method := dcSlideMethod memory (dcSchurGaussRadauEstimate memory mu upper (n := n))
    ContDiffAt ℝ r (fun z => (methodRun method (A z) (B z) (g z) N).gradient) x := by
  have hp := cgOperator_positive base hb
  exact smoothProbed_gradient_regular _ (dc_slide_consistent memory hm _) A B g x N hA hB hg
    (cgOperator base) hAx hBx hp.1 hp.2 hpre
    (dc_schur_slide_smoothCycleAt memory hm base hb mu upper hmu hmuL hlo hhi (g x) N hpre r)

end
end krylov.Cancellation
