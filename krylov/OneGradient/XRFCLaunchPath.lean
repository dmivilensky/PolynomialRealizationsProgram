import krylov.OneGradient.XRFCColumns
import krylov.Stability.ContDiffXRFC
import krylov.Stability.ContDiffSpectralMatrix
import krylov.Stability.MetricRootRegularity
import krylov.Correction.FullReconstruction
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, primitive actual full-cycle XRFC launch data.
Use: derive the real chronological evaluated-column and incoming-gradient
regularity on arbitrary smooth physical operator paths at genuine full-atom references.
Source: the existing actual primitive-trial query induction and true quadratic
basis domains, composed with the real finite spectral coordinate equivalence.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Correction
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {r : WithTop ℕ∞}

/-- The actual chronological physical evaluated-step matrix on an original
varying-operator XRFC trajectory.
Use: the general launch theorem receives actual recorded data, not a presumed moving basis.
Article: main_krylov, thm:I. -/
def xrfcPathColumns (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fullBasisMatrix (fun i : Fin n => oneGradientStep (xrfcMethod fullMemory trial)
    (fun k => cgOperator (A t k)) g i.val)

/-- The actual moving evaluated-step matrix has exactly the original
static reference evaluated columns at the quadratic base.
Use: all real inverse domains and original source oblique flags have the correct reference values.
Article: main_krylov, thm:I.
Proof: substitute the actual original constant reference operator into the true executor. -/
theorem xrfc_path_columns_reference
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ) (hA0 : ∀ k,A 0 k=base)
    (g : EuclideanSpace ℝ (Fin n)) :
    xrfcPathColumns trial A g 0=xrfcPhysicalColumns trial base g := by
  have he : (fun k => cgOperator (A 0 k))=(fun _ => cgOperator base) := funext (fun k => by rw [hA0])
  unfold xrfcPathColumns
  rw [he]
  rfl

/-- The actual full-cycle XRFC evaluated columns and incoming gradient are
C-r from primitive smooth physical operators and original observed trial charts.
Use: the general true launch expansion applies to the genuine implemented
varying-prefix trajectory, with all inverse domains derived from actual full atoms.
Article: main_krylov, thm:I, primitive trajectory regularity.
Proof: convert primitive physical matrices to their real query operators;
the actual nonzero-trial quadratic query induction gives every genuine
returned gradient and recorded step. The existing finite spectral coordinate
equivalence assembles the true chronological matrix without changing the perturbation norm. -/
theorem xrfc_launch_data_contDiff
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ r (fun t => A t k) 0) (hA0 : ∀ k,A 0 k=base)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    ContDiffAt ℝ r (xrfcPathColumns trial A g) 0 ∧
      ContDiffAt ℝ r (fun t => oneGradientGradient (xrfcMethod fullMemory trial)
        (fun k => cgOperator (A t k)) g n) 0 := by
  let m := xrfcMethod fullMemory trial
  let op := fun t k => cgOperator (A t k)
  have hAx : op 0=(fun _ => cgOperator base) := funext (fun k => by simp only [op,hA0])
  have hp := cgOperator_positive base hb
  have hreg := quadraticXRFC_prefix_contDiffAt trial op (fun _ => g) 0
    (fun k => matrixOperator_contDiffAt _ 0 (hA k)) contDiffAt_const (cgOperator base) hAx hp.1 hp.2 n
    (fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)) ht (by rw [hAx];exact hT)
  refine ⟨?_,hreg.1 n le_rfl⟩
  apply contDiff_spectral_matrix
  intro i j
  change ContDiffAt ℝ r (fun t => (oneGradientStep m (op t) g j.val) i) 0
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  have he := e.toContinuousLinearMap.contDiff.contDiffAt.comp 0 (hreg.2 j.val j.isLt)
  exact contDiffAt_pi.mp he i

end
end krylov.OneGradient
