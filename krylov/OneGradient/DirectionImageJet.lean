import krylov.Stability.DirectionCoefficientRegularity
import krylov.Stability.ZeroProductJet
import krylov.Methods.DirectionWeights
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, genuine first jet of the original direction replay.
Use: derive the varying-prefix error recurrence by differentiating the actual
native one-gradient transcript under primitive observed trial regularity.
Source: real replay-error identity, true primitive C1 query/coefficient
calculus, actual zero reference errors and the proved zero-product jet rule.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual original direction-replay image error has its genuine
frozen-native-coefficient first jet on arbitrary C1 physical operator paths.
Use: only real observed trial charts, true positive quadratic reference data
and actual nonzero reference trials are hypotheses.
Article: main_krylov, thm:I, differentiated exact image-error recursion.
Proof: genuine query induction and native inverse calculus give all actual
replay and coefficient derivatives. Every true reference error and drift
bracket is zero, so the real local nonzero-trial recursion differentiates
with frozen native coefficients and actual frozen CG directions. -/
theorem xrfcD_image_error_first_jet
    (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (hA : ∀ i,ContDiffAt ℝ 1 (fun t => A t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => Q) g k))
    (j : ℕ) (hj : j<N) :
    trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g j) •
      deriv (fun t => xrfcDImageError trial (A t) g j) 0=
      ∑ i : Fin j,xrfcDArrayCoefficients trial (fun _ => Q) g j i •
        ((deriv (fun t => A t j) 0-deriv (fun t => A t (j-1-i.val)) 0)
          (CG.direction Q g (j-1-i.val))-
          deriv (fun t => xrfcDImageError trial (A t) g (j-1-i.val)) 0) := by
  let m := xrfcDMethod fullMemory trial
  have hcharts : ∀ k<N,ContDiffAt ℝ 1 (trialCoordinate trial k) (oneGradientData m (A 0) g k) := by
    rw [hA0]
    exact hT
  have hreg := quadraticXRFCD_prefix_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const
    Q hA0 hQ hpos N hpre ht hcharts
  have hI (k : ℕ) (hk : k<N) : ContDiffAt ℝ 1 (fun t => xrfcDImageError trial (A t) g k) 0 :=
    (hreg.2.2.2 k hk).sub ((hA k).clm_apply (hreg.2.2.1 k hk))
  have hI0 (k : ℕ) (hk : k<N) : xrfcDImageError trial (A 0) g k=0 := by
    rw [hA0,xrfcDImageError,xrfcD_executed_image_reference trial Q hQ hpos g N hpre ht k hk,
      xrfcD_executed_direction_reference trial Q hQ hpos g N hpre ht k hk.le,sub_self]
  let tau := fun t => trial (oneGradientRun m (A t) g j)
  let w := fun t => xrfcDArrayCoefficients trial (A t) g j
  let F := fun t (i : Fin j) =>
    (A t j-A t (j-1-i.val)) (xrfcDExecutedDirection trial (A t) g (j-1-i.val))-
      xrfcDImageError trial (A t) g (j-1-i.val)
  have htau : ContDiffAt ℝ 1 tau 0 := actual_trial_contDiffAt trial m A (fun _ => g) 0 j
    contDiffAt_const (fun i hi => hreg.2.1 i (hi.trans hj))
    (fun i hi => hreg.1 i (hi.trans hj.le)) (hcharts j hj)
  have hw (i : Fin j) : ContDiffAt ℝ 1 (fun t => w t i) 0 :=
    quadraticXRFCD_coefficients_contDiffAt trial A (fun _ => g) 0 hA contDiffAt_const Q hA0 hQ hpos
      N hpre ht hcharts j hj.le i
  have hF (i : Fin j) : ContDiffAt ℝ 1 (fun t => F t i) 0 :=
    ((hA j).sub (hA (j-1-i.val))).clm_apply (hreg.2.2.1 _ (by omega)) |>.sub (hI _ (by omega))
  have hF0 (i : Fin j) : F 0 i=0 := by
    change (A 0 j-A 0 (j-1-i.val)) _-xrfcDImageError trial (A 0) g (j-1-i.val)=0
    rw [show A 0 j=A 0 (j-1-i.val) by simp only [hA0],sub_self,_root_.zero_apply,hI0 _ (by omega),sub_self]
  have hlocal : (fun t => tau t • xrfcDImageError trial (A t) g j)=ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ i : Fin j,w t i • F t i) := by
    have htau0 : tau 0≠0 := by dsimp only [tau];rw [hA0];exact ht j hj
    filter_upwards [htau.continuousAt.eventually_ne htau0] with t htn
    exact xrfcD_image_error_recursion trial (A t) g j htn
  have h := weighted_zero_identity_deriv tau (fun t => xrfcDImageError trial (A t) g j) w F
    (htau.differentiableAt (by norm_num)) ((hI j hj).differentiableAt (by norm_num))
    (fun i => (hw i).differentiableAt (by norm_num)) (fun i => (hF i).differentiableAt (by norm_num))
    (hI0 j hj) hF0 hlocal
  have hjet (i : Fin j) : deriv (fun t => F t i) 0=
      (deriv (fun t => A t j) 0-deriv (fun t => A t (j-1-i.val)) 0)
        (CG.direction Q g (j-1-i.val))-
        deriv (fun t => xrfcDImageError trial (A t) g (j-1-i.val)) 0 := by
    have h' := zero_drift_action_deriv (fun t => A t j) (fun t => A t (j-1-i.val))
      (fun t => xrfcDExecutedDirection trial (A t) g (j-1-i.val))
      (fun t => xrfcDImageError trial (A t) g (j-1-i.val))
      ((hA j).differentiableAt (by norm_num)) ((hA _).differentiableAt (by norm_num))
      ((hreg.2.2.1 _ (by omega)).differentiableAt (by norm_num))
      ((hI _ (by omega)).differentiableAt (by norm_num)) (by simp only [hA0])
    rw [hA0,xrfcD_executed_direction_reference trial Q hQ hpos g N hpre ht _ (by omega)] at h'
    exact h'
  simpa only [hjet,tau,w,hA0] using h

end
end krylov.OneGradient
