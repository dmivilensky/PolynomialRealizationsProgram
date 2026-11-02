import krylov.OneGradient.SchurHarmonicReference
import krylov.OneGradient.XRFCTwoBasisOutput
import krylov.Stability.ContDiffXRFC
import krylov.Stability.ContDiffXRFCD
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau and lem:U(d), executable smooth harmonic trials.
Use: derive native primitive trial regularity in both original XRFC bases and
actual trajectory smoothness from genuine physical spectral-band references.
Source: globally positive history-only Schur continuation, real quadratic
basis/history geometry and the proved actual observed-coordinate compiler. -/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Cancellation
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual native harmonic trial has primitive C-r trial coordinates
at every true active quadratic prefix, in either original stored basis.
Use: no trajectory, model-domain or trial regularity hypothesis is supplied.
Article: main_krylov, thm:radau and lem:U(d).
Proof: the positive actual policy derives the independent full CG basis.
Both native quadratic histories coincide. Real observed Schur regularity
and the exact complete-history/one-gradient chart bridge give the result. -/
theorem xrfc_schur_trial_reference_contDiff (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (k : ℕ) (hk : k<N) (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (trialCoordinate (xrfcSchurTrial mu upper) k)
      (oneGradientData (xrfcBasisMethod directions (xrfcSchurTrial mu upper)) (fun _ => cgOperator base) g k) := by
  let trial := xrfcSchurTrial mu upper (n := n)
  let method := xrfcBasisMethod directions trial
  let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k
  have hp := cgOperator_positive base hb
  have ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0 :=
    fun _ _ => (xrfc_schur_trial_positive mu upper _).ne'
  have hH : oneGradientRun method (fun _ => cgOperator base) g k=H := by
    cases directions with
    | false => rfl
    | true => exact xrfc_quadratic_basis_histories trial (cgOperator base) hp.1 hp.2 g N hpre ht k hk.le
  have hbasis := xrfc_full_basis trial (cgOperator base) hp.1 hp.2 g N hpre ht k hk.le
  apply trialCoordinate_of_history_estimate
  have hc : oneGradientHistoryChart (oneGradientData method (fun _ => cgOperator base) g k)=H := by
    change oneGradientHistoryChart (g,(fun i : Fin k => oneGradientStep method (fun _ => cgOperator base) g (k-1-i.val)),
      (fun i : Fin k => oneGradientGradient method (fun _ => cgOperator base) g (k-i.val)))=H
    rw [← oneGradientRun_chart]
    exact hH
  change ContDiffAt ℝ r (historyEstimateChart trial
    (oneGradientHistoryChart (oneGradientData method (fun _ => cgOperator base) g k)).queryShape
    (oneGradientHistoryChart (oneGradientData method (fun _ => cgOperator base) g k)).observationList.length)
    (observedArray _ (oneGradientHistoryChart (oneGradientData method (fun _ => cgOperator base) g k)).observationList)
  rw [hc]
  exact xrfc_schur_actual_reference_regular H base hb g k (fun i hi => hpre i (by omega)) mu upper hmu hmuL hlo hhi
    (oneGradientRun_quadratic_gradient _ _ _ _) (fun j => oneGradientRun_pairs_quadratic _ _ _ _
      (H.pairs.get j) (List.get_mem _ j)) hbasis.1 hbasis.2 r

/-- Native step-basis XRFC with the actual continued harmonic policy has
C-r queried steps and returned gradients at every physical active reference.
Use: r=two supplies the genuine local remainder hypotheses of the original
XRFC interval implementation without assuming smooth selected lengths.
Article: main_krylov, thm:radau and lem:U(d).
Proof: true policy positivity and the proved native primitive trial charts
supply all original hypotheses of the actual quadratic XRFC smooth compiler. -/
theorem xrfc_schur_prefix_contDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : X → EuclideanSpace ℝ (Fin n)) (x : X) (r : WithTop ℕ∞)
    (hA : ∀ i,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hAx : A x=fun _ => cgOperator base)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) (g x) i≠0) :
    (∀ k≤N,ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcMethod fullMemory (xrfcSchurTrial mu upper)) (A z) (g z) k) x) ∧
      ∀ i<N,ContDiffAt ℝ r (fun z => oneGradientStep (xrfcMethod fullMemory (xrfcSchurTrial mu upper)) (A z) (g z) i) x := by
  have hp := cgOperator_positive base hb
  apply quadraticXRFC_prefix_contDiffAt (xrfcSchurTrial mu upper) A g x hA hg (cgOperator base) hAx hp.1 hp.2 N hpre
    (fun _ _ => (xrfc_schur_trial_positive mu upper _).ne')
  intro k hk
  rw [hAx]
  exact xrfc_schur_trial_reference_contDiff false base hb mu upper hmu hmuL hlo hhi (g x) N hpre k hk r

/-- Native direction-basis XRFC with the same genuine harmonic policy has
C-r actual queried steps and returned gradients at the physical reference.
Use: both original interval implementations have all trajectory regularity
derived from their primitive data, including genuine replay image inverses.
Article: main_krylov, thm:radau and lem:U(d).
Proof: the positive policy and its proved direction-basis primitive trial
charts feed the genuine direction-replay smooth execution compiler. -/
theorem xrfc_schur_direction_prefix_contDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : X → EuclideanSpace ℝ (Fin n)) (x : X) (r : WithTop ℕ∞)
    (hA : ∀ i,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hAx : A x=fun _ => cgOperator base)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) (g x) i≠0) :
    (∀ k≤N,ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcDMethod fullMemory (xrfcSchurTrial mu upper)) (A z) (g z) k) x) ∧
      ∀ i<N,ContDiffAt ℝ r (fun z => oneGradientStep (xrfcDMethod fullMemory (xrfcSchurTrial mu upper)) (A z) (g z) i) x := by
  have hp := cgOperator_positive base hb
  have h := quadraticXRFCD_prefix_contDiffAt (xrfcSchurTrial mu upper) A g x hA hg
    (cgOperator base) hAx hp.1 hp.2 N hpre
    (fun _ _ => (xrfc_schur_trial_positive mu upper _).ne')
    (fun k hk => by
      rw [hAx]
      exact xrfc_schur_trial_reference_contDiff true base hb mu upper hmu hmuL hlo hhi (g x) N hpre k hk r)
  exact ⟨h.1,h.2.1⟩

end
end krylov.OneGradient
