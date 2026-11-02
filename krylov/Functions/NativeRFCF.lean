import krylov.Functions.NativeRFCExecution
import krylov.Functions.TrapezoidAffine
import krylov.Correction.TerminalModelQuery

/-!
Article: main_krylov, prop:Fcycle, the genuine last-correction RFC-F executor.
Use: retain the complete actual ordinary-RFC prefix, replace only its final
model by the model computed from actual endpoint values, and evaluate the
true gradient at the actual returned point. The model receives no Hessian,
third derivative, prescribed trajectory or leading response.
Source: equation (function-value-model) and Algorithm FC; oldest-first
finite indexing agrees with the existing latest-information construction.
-/

namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual oldest-first anchors retained before the final RFC-F correction.
Article: main_krylov, prop:Fcycle. -/
def rfcFAnchors (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (i : Fin (k+1)) : E :=
  rfcFunctionPoint T f G fullMemory r x₀ i.val

/-- Every old pair uses its actual total corrected step; the newest pair is
its actual searched segment, before the final correction.
Article: main_krylov, prop:Fcycle, unchanged intermediate RFC corrections. -/
def rfcFSteps (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (i : Fin (k+1)) : E :=
  if i.val<k then rfcFunctionPoint T f G fullMemory r x₀ (i.val+1)-rfcFAnchors T f G r x₀ k i
  else rfcFunctionLineStep T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ k)

/-- The genuine endpoint before the last value-informed correction.
Article: main_krylov, prop:Fcycle. -/
def rfcFAnchor (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  rfcFunctionLinePoint T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ k)

/-- The actual model-metric split, computed from the observed gradient secant.
Article: main_krylov, equation (function-value-model), lambda^Y. -/
def rfcFSplit (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (i : Fin (k+1)) : ℝ :=
  let a := rfcFAnchors T f G r x₀ k i
  let s := rfcFSteps T f G r x₀ k i
  covectorSplit (innerSL ℝ (G (a+s)-G a)) a s (rfcFAnchor T f G r x₀ k)

/-- The genuine RFC-F final model, using exactly the true endpoint values
and true endpoint gradients of its retained pairs.
Article: main_krylov, equation (function-value-model). -/
def rfcFModel (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  valueCorrectedModel f (fun x => innerSL ℝ (G x)) (rfcFAnchors T f G r x₀ k)
    (rfcFSteps T f G r x₀ k) (rfcFSplit T f G r x₀ k)

/-- The actual RFC-F terminal correction, with the same observed gate as RFC.
Article: main_krylov, prop:Fcycle. The solve is totalized by the existing
model solver exactly as in the original RFC executor. -/
def rfcFCorrectionStep (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E := by
  classical
  exact if rfcFunctionGate fullMemory (rfcFunctionRun T f G fullMemory r x₀ k) then
    combine (rfcFSteps T f G r x₀ k) (modelCoefficients (rfcFSteps T f G r x₀ k)
      (rfcFModel T f G r x₀ k) (G (rfcFAnchor T f G r x₀ k))) else 0

/-- The actual scalar-function RFC-F output after the genuine unchanged RFC prefix.
Article: main_krylov, prop:Fcycle. -/
def rfcFPoint (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  rfcFAnchor T f G r x₀ k+rfcFCorrectionStep T f G r x₀ k

/-- Every old retained segment has precisely its actually observed next endpoint.
Article: main_krylov, prop:Fcycle, exact pair/oracle dictionary. -/
theorem rfcFSteps_old_endpoint (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (i : Fin (k+1)) (hi : i.val<k) :
    rfcFAnchors T f G r x₀ k i+rfcFSteps T f G r x₀ k i=
      rfcFunctionPoint T f G fullMemory r x₀ (i.val+1) := by
  simp only [rfcFSteps,hi,ite_true,add_sub_cancel]

/-- The newest observed segment ends exactly at the actual last searched point.
Article: main_krylov, prop:Fcycle, no fictitious probe segment. -/
theorem rfcFSteps_last_endpoint (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    rfcFAnchors T f G r x₀ k (Fin.last k)+rfcFSteps T f G r x₀ k (Fin.last k)=
      rfcFAnchor T f G r x₀ k := by
  simp only [rfcFSteps,Fin.val_last,lt_self_iff_false,ite_false,rfcFAnchors,rfcFunctionLineStep,
    rfcFunctionPoint,rfcFAnchor,add_sub_cancel]

/-- The actual model-metric split annihilates the observed secant component.
Article: main_krylov, prop:Fcycle, w_i perpendicular to y_i. -/
theorem rfcFSplit_orthogonal (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (i : Fin (k+1))
    (h : inner ℝ (G (rfcFAnchors T f G r x₀ k i+rfcFSteps T f G r x₀ k i)-
      G (rfcFAnchors T f G r x₀ k i)) (rfcFSteps T f G r x₀ k i)≠0) :
    inner ℝ (G (rfcFAnchors T f G r x₀ k i+rfcFSteps T f G r x₀ k i)-
      G (rfcFAnchors T f G r x₀ k i))
      (rfcFAnchor T f G r x₀ k-(rfcFAnchors T f G r x₀ k i+
        (1/2:ℝ) • rfcFSteps T f G r x₀ k i)-
        rfcFSplit T f G r x₀ k i • rfcFSteps T f G r x₀ k i)=0 :=
by
  simpa only [rfcFSplit,innerSL_apply_apply] using
    covectorSplit_annihilates (innerSL ℝ (G (rfcFAnchors T f G r x₀ k i+rfcFSteps T f G r x₀ k i)-
      G (rfcFAnchors T f G r x₀ k i))) (rfcFAnchors T f G r x₀ k i)
      (rfcFSteps T f G r x₀ k i) (rfcFAnchor T f G r x₀ k) h

/-- The real corrected-model coefficients satisfy their exact normal equation.
Article: main_krylov, prop:Fcycle. Only the actual inverse domain is needed;
no output expansion or trajectory estimate is a premise. -/
theorem rfcFModel_coefficients_equation (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ)
    (hM : IsUnit (rfcFModel T f G r x₀ k).det) :
    (rfcFModel T f G r x₀ k)*ᵥ
      modelCoefficients (rfcFSteps T f G r x₀ k) (rfcFModel T f G r x₀ k)
        (G (rfcFAnchor T f G r x₀ k))=
      -coordinates (rfcFSteps T f G r x₀ k) (G (rfcFAnchor T f G r x₀ k)) := by
  rw [modelCoefficients,Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hM,
    Matrix.one_mulVec]

/-- An accepted actual gate executes precisely the observed value-corrected solve.
Article: main_krylov, prop:Fcycle, faithful final-correction dictionary. -/
theorem rfcFCorrectionStep_eq (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ)
    (hgate : rfcFunctionGate fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)) :
    rfcFCorrectionStep T f G r x₀ k=
      combine (rfcFSteps T f G r x₀ k) (modelCoefficients (rfcFSteps T f G r x₀ k)
        (rfcFModel T f G r x₀ k) (G (rfcFAnchor T f G r x₀ k))) := by
  simp only [rfcFCorrectionStep,hgate,ite_true]

end
end krylov.Functions
