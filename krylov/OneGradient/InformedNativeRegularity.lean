import krylov.OneGradient.NativeLastLaunch
import krylov.OneGradient.InformedCalibration
import krylov.Stability.ContDiffXRFC
import krylov.Stability.ContDiffXRFCD
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), primitive both-native incoming data calculus.
Use: derive every actual old array, incoming-gradient and trial chart
needed by the original shared final-launch row computation.
Source: genuine informed observed trial regularity and actual S/D prefix
query/replay induction, with all true reference inverse domains derived.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- Actual informed S/D incoming gradients, old native columns and images,
and real selected trials are C-one from only primitive physical operators.
No coefficient, replay, direction or trajectory regularity is assumed.
Use: all native hypotheses of the primitive last-launch row theorem are
derived on the original full perturbation space in either actual basis.
Article: main_krylov, thm:local(a), genuine native incoming regularity.
Proof: true positive reference geometry and primitive informed trial
charts give the actual S or D query induction. Select the true old
newest-age entries; real step images use actual operator application.
The true finite observed-data trial chart gives the selected trial itself. -/
theorem informed_native_prefix_contDiff (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcBasisMethod directions trial
    (∀ k≤ N,ContDiffAt ℝ 1 (fun z => oneGradientGradient m (A z) g k) 0) ∧
      (∀ k≤ N,∀ i : Fin k,
        ContDiffAt ℝ 1 (fun z => xrfcNativeColumns directions trial (A z) g k i) 0 ∧
          ContDiffAt ℝ 1 (fun z => xrfcNativeImages directions trial (A z) g k i) 0) ∧
      ∀ k<N,ContDiffAt ℝ 1 (fun z => trial (oneGradientRun m (A z) g k)) 0 := by
  let trial := informedTrial (cgOperator base)
  have hp := cgOperator_positive base hb
  cases directions with
  | false =>
    let m := xrfcMethod fullMemory trial
    have hcharts : ∀ k<N,ContDiffAt ℝ 1 (trialCoordinate trial k) (oneGradientData m (A 0) g k) := by
      rw [hA0]
      exact fun k hk => informed_trial_reference_contDiff false base hb base hb g N hpre k hk 1
    have hreg := quadraticXRFC_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
      (cgOperator base) hA0 hp.1 hp.2 N hpre (fun _ _ => (informed_trial_positive (cgOperator base) _).ne') hcharts
    refine ⟨hreg.1,?_,?_⟩
    · intro k hk i
      exact ⟨hreg.2 _ (by omega),(hA _).clm_apply (hreg.2 _ (by omega))⟩
    · intro k hk
      exact actual_trial_contDiffAt trial m A (fun _ => g) 0 k contDiffAt_const
        (fun j hj => hreg.2 j (hj.trans hk)) (fun j hj => hreg.1 j (hj.trans hk.le)) (hcharts k hk)
  | true =>
    let m := xrfcDMethod fullMemory trial
    have hcharts : ∀ k<N,ContDiffAt ℝ 1 (trialCoordinate trial k) (oneGradientData m (A 0) g k) := by
      rw [hA0]
      exact fun k hk => informed_trial_reference_contDiff true base hb base hb g N hpre k hk 1
    have hreg := quadraticXRFCD_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
      (cgOperator base) hA0 hp.1 hp.2 N hpre (fun _ _ => (informed_trial_positive (cgOperator base) _).ne') hcharts
    refine ⟨hreg.1,?_,?_⟩
    · intro k hk i
      exact ⟨hreg.2.2.1 _ (by omega),hreg.2.2.2 _ (by omega)⟩
    · intro k hk
      exact actual_trial_contDiffAt trial m A (fun _ => g) 0 k contDiffAt_const
        (fun j hj => hreg.2.1 j (hj.trans hk)) (fun j hj => hreg.1 j (hj.trans hk.le)) (hcharts k hk)

end
end krylov.OneGradient
