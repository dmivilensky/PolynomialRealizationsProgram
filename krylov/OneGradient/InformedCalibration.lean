import krylov.OneGradient.InformedTrial
import krylov.LinearAlgebra.RelativeCurvature
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine informed calibration and regularity.
Use: derive native informed trial smoothness in both XRFC bases at the true
A0 reference, independently of the known base, and exact prior-wide calibration.
Source: original positive data-only policy, actual quadratic CG histories,
real observed model domains and genuine physical relative-curvature bounds. -/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Cancellation krylov.LinearAlgebra krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual informed policy has primitive C-r trial coordinates at every
active quadratic reference in either native basis, with independent known base.
Use: all primitive smoothness premises of the source informed analysis are
derived at the actual A0, rather than assumed or proved only at the known A.
Article: main_krylov, thm:local(a) and lem:U(d).
Proof: positivity gives the real independent CG basis and equal S/D histories.
The actual known curvature quotient is positive. True quadratic observations
give both genuine model domains; compose the proved complete-history calculus. -/
theorem informed_trial_reference_contDiff (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (known : Matrix (Fin n) (Fin n) ℝ) (hknown : known.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (k : ℕ) (hk : k<N) (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (trialCoordinate (informedTrial (cgOperator known)) k)
      (oneGradientData (xrfcBasisMethod directions (informedTrial (cgOperator known))) (fun _ => cgOperator base) g k) := by
  let trial := informedTrial (cgOperator known)
  let method := xrfcBasisMethod directions trial
  let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k
  have hp := cgOperator_positive base hb
  have ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0 :=
    fun _ _ => (informed_trial_positive (cgOperator known) _).ne'
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
  have hknownOp := cgOperator_positive known hknown
  have hraw := (informed_trial_quadratic_values (cgOperator known) (cgOperator base) hknownOp.2 hp.1 hp.2
    g N hpre k hk).1
  have hy : ∀ j,windowImages H.pairs j=cgOperator base (windowSteps H.pairs j) := fun j =>
    oneGradientRun_pairs_quadratic _ _ _ _ (H.pairs.get j) (List.get_mem _ j)
  have hmodel := operatorGram_posDef (cgOperator base) hp.1 hp.2 hbasis.1
  apply informed_trial_history_regular (cgOperator known) hknownOp.2 H r _ _ hraw
  · rw [windowModel_quadratic H.pairs (cgOperator base) hp.1 hy]
    exact hmodel.det_pos.ne'
  · rw [show windowImages H.pairs=(fun j => cgOperator base (windowSteps H.pairs j)) from funext hy]
    exact hmodel.det_pos.ne'

/-- Every genuine informed reference trial error is bounded by the exact
physical known-base relative budget, at every active prefix in either basis.
Use: a prior bound c*omega derives all original O(omega) reference trial
errors uniformly, without a supplied error sequence or smoothness premise.
Article: main_krylov, thm:local(a).
Proof: the actual positive policy gives the true CG virtual inputs on the
real A0 reference. Its exact curvature-error identity and the genuine relative
Rayleigh bound apply to the actual nonzero CG direction. Complete quadratic
history equality transfers the same actual decisions to the direction basis. -/
theorem informed_reference_trial_error_bound (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (known : Matrix (Fin n) (Fin n) ℝ) (hknown : known.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (k : ℕ) (hk : k<N) :
    let trial := informedTrial (cgOperator known)
    let H := oneGradientRun (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k
    |1-trial H/CG.length (cgOperator base) g k|≤relativeBudget known (base-known) := by
  let trial := informedTrial (cgOperator known)
  have hp := cgOperator_positive base hb
  have hkp := cgOperator_positive known hknown
  have he := (informed_trial_quadratic_values (cgOperator known) (cgOperator base) hkp.2 hp.1 hp.2
    g N hpre k hk).2.2
  have hd := (CG.invariant_line_pos (cgOperator base) hp.2 g k
    (CG.invariant (cgOperator base) hp.1 hp.2 g k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).1
  have hbnd := relative_curvature_quotient_bound known (base-known) hknown (CG.direction (cgOperator base) g k) hd
  have hop : cgOperator base-cgOperator known=cgOperator (base-known) := by simp only [cgOperator,map_sub]
  rw [hop] at he
  cases directions with
  | false =>
    change |1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)/
      CG.length (cgOperator base) g k|≤_
    rw [he]
    exact hbnd
  | true =>
    change |1-trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator base) g k)/
      CG.length (cgOperator base) g k|≤_
    rw [xrfc_quadratic_basis_histories trial (cgOperator base) hp.1 hp.2 g N hpre
      (fun _ _ => (informed_trial_positive (cgOperator known) _).ne') k hk.le,he]
    exact hbnd

end
end krylov.OneGradient
