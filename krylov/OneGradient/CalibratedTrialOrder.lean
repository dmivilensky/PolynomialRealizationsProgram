import krylov.OneGradient.CalibratedErrorRegularity
import krylov.OneGradient.FixedCGTrial
import krylov.Stability.MetricRootRegularity
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine calibrated measured-error orders.
Use: primitive calibrated observed rules give the actual first-order
native relative trial errors required by the general cubic output formula.
Source: genuine native error regularity, its true zero reference value
and standard differentiability's first-order bound, in full parameter norm.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Stability krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every actual measured native trial error of a primitive calibrated
history-only rule is first order in the whole perturbation parameter.
Use: the general theorem's small relative errors are derived, rather than
supplied as a sequence or a trajectory expansion.
Article: main_krylov, thm:local(a), actual epsilon is O(norm(z)).
Proof: the true observed native error is C-one and exactly zero at the
known quadratic reference. Apply the genuine differentiable first-order bound. -/
theorem calibrated_native_error_first_order (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (hcal : CalibratedTrial trial (cgOperator base) g N)
    (hT : ∀ (directions : Bool) (k : ℕ),k<N → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (k : ℕ) (hk : k<N) :
    (fun z => xrfcNativeTrialError directions trial (A z) g k) =O[𝓝 0] (fun z => ‖z‖) := by
  have h := calibrated_native_error_data directions trial base hb g N hpre hcal hT A hA hA0 k hk
  simpa only [h.2,sub_zero] using (h.1.differentiableAt (by norm_num)).isBigO_sub.norm_right

/-- In particular, the actual fixed known-CG trial errors on every moving
quadratic reference are first order, in either native basis. The real
reference histories are executed with their own moving base operators.
Use: derive the source's fixed-alpha-known comparison from primitive
moving bases, without a prescribed reference trial-error sequence.
Article: main_krylov, thm:local(a), actual fixed known-reference errors.
Proof: the literal fixed rule has genuine calibration and constant smooth
trial charts. Apply the actual native error order to the true constant-in-
query moving quadratic operator family. -/
theorem fixedCGTrial_moving_reference_errors_first_order (directions : Bool)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (B : X → Matrix (Fin n) (Fin n) ℝ) (hB : ContDiffAt ℝ 1 B 0) (hB0 : B 0=base)
    (k : ℕ) (hk : k<N) :
    (fun z => xrfcNativeTrialError directions (fixedCGTrial base g) (fun _ => cgOperator (B z)) g k)
      =O[𝓝 0] (fun z => ‖z‖) := by
  exact calibrated_native_error_first_order directions (fixedCGTrial base g) base hb g N hpre
    (fixedCGTrial_calibrated base g N) (fun _ j _ => (fixedCGTrial_contDiff base g j).contDiffAt)
    (fun z _ => cgOperator (B z)) (fun _ => matrixOperator_contDiffAt _ 0 hB)
    (by rw [hB0]) k hk

/-- One genuine radius and constant control all actual reference trial
errors of a primitive calibrated rule over every unknown quadratic base
in the original relative-matrix ball. The entire active prefix is uniform.
Use: an original prior budget c*omega gives true reference errors O(c*omega),
including the fixed known-CG rule, without any smooth unknown-base path.
Article: main_krylov, thm:local(a), original uniform reference-error premise.
Proof: use the full relative-matrix coordinate space and derive C-one
actual error coordinates from primitive calibrated observed charts. Their
true zero reference gives a common finite-prefix first-order bound. The
exact root-congruence reconstruction embeds every real unknown base with
parameter norm equal to its original relative prior budget. -/
theorem calibrated_quadratic_reference_error_bound (directions : Bool)
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0)
    (hcal : CalibratedTrial trial (cgOperator base) g N)
    (hT : ∀ (directions : Bool) (k : ℕ),k<N → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k)) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ B : Matrix (Fin n) (Fin n) ℝ,
      relativeBudget base (B-base)<delta → ∀ k<N,
      |xrfcNativeTrialError directions trial (fun _ => cgOperator B) g k|≤C*relativeBudget base (B-base) := by
  let B := fun Z : Matrix (Fin n) (Fin n) ℝ => base+metricRoot base*Z*metricRoot base
  let A := fun Z (_ : ℕ) => cgOperator (B Z)
  let error := fun Z (k : Fin N) => xrfcNativeTrialError directions trial (A Z) g k.val
  have hB : ContDiffAt ℝ 1 B 0 := contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_id).mul contDiffAt_const)
  have hB0 : B 0=base := by simp only [B,Matrix.mul_zero,Matrix.zero_mul,add_zero]
  have hA : ∀ j,ContDiffAt ℝ 1 (fun Z => A Z j) 0 := fun _ => matrixOperator_contDiffAt _ 0 hB
  have hA0 : A 0=fun _ => cgOperator base := by dsimp only [A];rw [hB0]
  have hdata (k : Fin N) := calibrated_native_error_data directions trial base hb g N hpre hcal hT A hA hA0 k.val k.isLt
  have herr : ContDiffAt ℝ 1 error 0 := contDiffAt_pi.mpr fun k => (hdata k).1
  have he0 : error 0=0 := funext fun k => (hdata k).2
  have ho : error =O[𝓝 0] (fun Z => ‖Z‖) := by
    simpa only [he0,sub_zero] using (herr.differentiableAt (by norm_num)).isBigO_sub.norm_right
  obtain ⟨C,hC,hbound⟩ := isBigO_iff'.mp ho
  obtain ⟨delta,hd,hnear⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨delta,C,hd,hC,?_⟩
  intro Q hQ k hk
  let Z := relativeOperator base (Q-base)
  have hZ : ‖Z‖<delta := hQ
  have hrestore : B Z=Q := by
    dsimp only [B,Z]
    rw [relativeOperator_reconstruct base (Q-base) hb]
    abel
  have h := hnear (by simpa only [dist_zero_right] using hZ)
  have hkbound := (norm_le_pi_norm (error Z) (⟨k,hk⟩ : Fin N)).trans h
  change |xrfcNativeTrialError directions trial (fun _ => cgOperator Q) g k|≤C*‖Z‖
  simpa only [error,A,hrestore,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg Z)] using hkbound

end
end krylov.OneGradient
