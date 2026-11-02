import krylov.OneGradient.LaggedDomains
import krylov.Stability.LaggedTrialCharts
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb, unconditional native lagged trial regularity.
Use: supply the real primitive smooth trial hypotheses for both actual native
XRFC implementations from positive initialization and nonstagnation alone.
Source: proved actual replay domains and the original finite history chart.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {m : ℕ}

/-- The actual lagged rule has primitive C^r observed-coordinate regularity
at every genuine quadratic prefix in its original chosen basis.
Use: all native lagged Taylor and compact remainder theorems now have their
trial hypothesis proved, for every finite order and also C-infinity.
Article: main_krylov, prop:hb.
Proof: the complete replay domain follows from executed quadratic geometry;
the exact history-chart dictionary feeds it into the proved cache calculus. -/
theorem lagged_trial_reference_contDiff {r : WithTop ℕ∞} (directions : Bool)
    {tau0 : ℝ} (htau0 : 0<tau0)
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k≤N) :
    let trial := laggedTrial directions tau0
    let method := xrfcBasisMethod directions trial
    ContDiffAt ℝ r (trialCoordinate trial k) (oneGradientData method (fun _ => Q) g k) := by
  let method : OneGradientMethod (EuclideanSpace ℝ (Fin m)) :=
    xrfcBasisMethod directions (laggedTrial directions tau0)
  apply contDiff_laggedTrialCoordinate
  change laggedReplayDomain directions tau0 g
    (oneGradientHistoryChart (g,(fun i : Fin k => oneGradientStep method (fun _ => Q) g (k-1-i.val)),
      (fun i : Fin k => oneGradientGradient method (fun _ => Q) g (k-i.val)))).records
  rw [← oneGradientRun_chart]
  exact lagged_reference_domain directions htau0 Q hQ hpos g N hpre k hk

/-- The printed actual measured amplitude uses the same lagged previous CG
length in its step-history convention, for either original lagged policy.
Use: connect the original source amplitude products to the actual S/D policy.
Article: main_krylov, prop:hb.
Proof: the native measured-length theorem is exact; genuine complete
quadratic history equality transfers the D policy to the source S convention. -/
theorem lagged_trial_step_reference_next (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 → 0 < inner ℝ v (Q v))
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (k : ℕ) (hk : k<N) :
    let trial := laggedTrial directions tau0
    trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g (k+1))=CG.length Q g k := by
  cases directions with
  | false => exact lagged_trial_reference_next false htau0 Q hQ hpos g N hpre k hk
  | true =>
    let trial : History (EuclideanSpace ℝ (Fin m)) → ℝ := laggedTrial true tau0
    have he := xrfc_quadratic_basis_histories trial Q hQ hpos g N hpre
      (fun _ _ => (lagged_trial_positive true htau0 _).ne') (k+1) (by omega)
    change trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g (k+1))=_
    rw [← he]
    exact lagged_trial_reference_next true htau0 Q hQ hpos g N hpre k hk

end
end krylov.OneGradient
