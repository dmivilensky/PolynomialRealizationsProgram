import krylov.OneGradient.CalibratedDirectionCubic
import krylov.OneGradient.InformedDirectionError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine informed cubic replay contribution.
Use: retain the actual informed native virtual coefficients and real replay
images in the full cubic known-base contribution estimate.
Source: the true informed policy's derived native calibration/regularity
and the proved complete calibrated native contribution bound.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open Filter Topology Asymptotics
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The actual informed direction replay has its complete cubic weighted
image-error contribution in every real native prefix, from only primitive
C-one physical operators. Every trial/coefficient chart and reference
calibration premise is derived for the implemented history-only policy.
Use: closes the actual informed O(omega³) replay contribution in the source.
Article: main_krylov, thm:local(a), genuine informed direction basis.
Proof: actual S/D reference histories identify the informed true CG trial;
the proved primitive informed estimate calculus derives all real charts.
The genuine native weighted image-error theorem then gives cubic order. -/
theorem informed_direction_image_contribution_cubic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i< N,CG.gradient (cgOperator base) g i≠0)
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ i,ContDiffAt ℝ 1 (fun z => A z i) 0)
    (hA0 : A 0=fun _ => cgOperator base) (k : ℕ) (hk : k≤ N) :
    (fun z => ∑ i : Fin k,xrfcDArrayCoefficients (informedTrial (cgOperator base)) (A z) g k i •
      xrfcDImageError (informedTrial (cgOperator base)) (A z) g (k-1-i.val))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
  let trial := informedTrial (cgOperator base)
  have hp := cgOperator_positive base hb
  have htS : ∀ i< N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0 :=
    fun _ _ => (informed_trial_positive (cgOperator base) _).ne'
  apply calibrated_direction_image_contribution_cubic trial A hA (cgOperator base) hA0 hp.1 hp.2 g N hpre
    (fun _ _ => (informed_trial_positive (cgOperator base) _).ne') ?_ ?_ k hk
  · intro i hi
    rw [xrfc_quadratic_basis_histories trial (cgOperator base) hp.1 hp.2 g N hpre htS i hi.le]
    exact (informed_trial_step_reference (cgOperator base) hp.1 hp.2 g N hpre i hi).2
  · intro j hj
    exact informed_trial_reference_contDiff true base hb base hb g N hpre j hj 1

end
end krylov.OneGradient
