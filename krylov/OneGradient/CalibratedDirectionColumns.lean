import krylov.OneGradient.CalibratedNativeImage
import krylov.OneGradient.XRFCColumns
import krylov.Correction.FullReconstruction
import krylov.Stability.ContDiffSpectralMatrix
import krylov.Stability.MetricRootRegularity
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine full calibrated direction columns.
Use: derive the actual chronological replay basis, images, smoothness,
inverse domain and quadratic image-matrix error from primitive operators.
Source: native calibrated query charts, genuine full quadratic direction
domains and the already proved actual quadratic replay-image estimate.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.LinearAlgebra krylov.Correction
open Filter Topology Asymptotics
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The true chronological native calibrated direction columns.
Use: the original direction output uses its actual replayed basis.
Article: main_krylov, thm:local(a), actual direction basis. -/
def calibratedDirectionColumns (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (z : X) :
    Matrix (Fin n) (Fin n) ℝ := fullBasisMatrix (fun i : Fin n =>
      xrfcDExecutedDirection trial (fun k => cgOperator (A z k)) g i.val)

/-- The true chronological native calibrated replay-image columns.
Use: no unobserved true operator images replace the implemented replay.
Article: main_krylov, thm:local(a), actual replayed images. -/
def calibratedDirectionImages (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (z : X) :
    Matrix (Fin n) (Fin n) ℝ := fullBasisMatrix (fun i : Fin n =>
      xrfcDExecutedImage trial (fun k => cgOperator (A z k)) g i.val)

/-- All actual calibrated full direction/image columns are C-one in the
full primitive operator parameter, their true reference image matrix is
the actual base action, and their genuine image-matrix error is quadratic.
Use: every replay-model comparison premise comes from the real native
executor and primitive data, rather than supplied trajectory estimates.
Article: main_krylov, thm:local(a), true direction launch data.
Proof: derive all calibrated native trial charts at the true quadratic
reference. Actual replay query induction gives genuine C-one vectors;
finite spectral coordinates assemble their real matrices. The genuine
quadratic image-error theorem transfers entrywise through true projections. -/
theorem calibrated_direction_columns_data
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (hcal : CalibratedTrial trial (cgOperator base) g (n))
    (hT : ∀ (directions : Bool) (k : ℕ),k<(n) → ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcBasisMethod directions trial) (fun _ => cgOperator base) g k))
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun z => A z k) 0) (hA0 : ∀ k,A 0 k=base) :
    let D := calibratedDirectionColumns trial A g
    let Y := calibratedDirectionImages trial A g
    ContDiffAt ℝ 1 D 0 ∧ ContDiffAt ℝ 1 Y 0 ∧ Y 0=pairImages (D 0) (A 0) ∧
      (fun z => Y z-pairImages (D z) (A z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let m := xrfcDMethod fullMemory trial
  let op := fun z k => cgOperator (A z k)
  let D := calibratedDirectionColumns trial A g
  let Y := calibratedDirectionImages trial A g
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 := fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hop : ∀ k,ContDiffAt ℝ 1 (fun z => op z k) 0 := fun k => matrixOperator_contDiffAt _ 0 (hA k)
  have hop0 : op 0=fun _ => cgOperator base := funext (fun k => congrArg cgOperator (hA0 k))
  have ht : ∀ i<n,trial (oneGradientRun m (fun _ => cgOperator base) g i)≠0 :=
    calibrated_native_reference_nonzero true trial (cgOperator base) hp.1 hp.2 g n hpre hcal
  have hcharts : ∀ i<n,ContDiffAt ℝ 1 (trialCoordinate trial i) (oneGradientData m (op 0) g i) := by
    rw [hop0]
    exact hT true
  have hreg := quadraticXRFCD_prefix_contDiffAt trial op (fun _ => g) 0 hop contDiffAt_const
    (cgOperator base) hop0 hp.1 hp.2 n hpre ht hcharts
  have hD : ContDiffAt ℝ 1 D 0 := by
    apply contDiff_spectral_matrix
    intro i j
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.contDiffAt.comp 0 (hreg.2.2.1 j.val j.isLt)
  have hY : ContDiffAt ℝ 1 Y 0 := by
    apply contDiff_spectral_matrix
    intro i j
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.contDiffAt.comp 0 (hreg.2.2.2 j.val j.isLt)
  refine ⟨hD,hY,?_,?_⟩
  · ext i j
    change (xrfcDExecutedImage trial (op 0) g j.val) i=
      (cgOperator (A 0 j.val) (xrfcDExecutedDirection trial (op 0) g j.val)) i
    rw [hop0,hA0,xrfcD_executed_image_reference trial _ hp.1 hp.2 g n hpre ht j.val j.isLt,
      xrfcD_executed_direction_reference trial _ hp.1 hp.2 g n hpre ht j.val j.isLt.le]
  · apply (matrix_bigO_iff_entry _ _).mpr
    intro i j
    have hi := calibrated_direction_image_quadratic trial op hop (cgOperator base) hop0 hp.1 hp.2 g n hpre ht
      (calibrated_native_reference_trial true trial _ hp.1 hp.2 g n hpre hcal) (hT true) j.val j.isLt
    have he := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).isBigO_comp
      (fun z => xrfcDImageError trial (op z) g j.val) (𝓝 0)).trans hi
    exact he

end
end krylov.OneGradient
