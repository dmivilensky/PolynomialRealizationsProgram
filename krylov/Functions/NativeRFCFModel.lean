import krylov.Functions.NativeRFCFReference
import krylov.Functions.RFCModifiedCorrection

/-!
Article: main_krylov, prop:Fcycle, exact actual observed-model input.
Use: identify the real chronological value-corrected solve with the original
raw probed-basis model change. Every diagonal entry is computed from the true
observed value defect and split; the newest searched segment contributes its
actual squared column scale. Source: exact reversal and inverse congruence,
valid also for totalized singular solves.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual additive value correction in chronological searched/retained-step coordinates.
Article: main_krylov, equation (function-value-model). -/
def rfcFValueDiagonal (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (i : Fin (k+1)) : ℝ :=
  -(12*rfcFSplit T f G r x₀ k i*
    segmentValueDefect f (fun x=>innerSL ℝ (G x)) (rfcFAnchors T f G r x₀ k i) (rfcFSteps T f G r x₀ k i))

/-- Every real retained value-model secant is the difference of its genuinely evaluated endpoint gradients.
Article: main_krylov, prop:Fcycle. -/
def rfcFImages (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (i : Fin (k+1)) : E :=
  G (rfcFAnchors T f G r x₀ k i+rfcFSteps T f G r x₀ k i)-G (rfcFAnchors T f G r x₀ k i)

/-- The true value-corrected model is its true latest secant matrix plus its actual observed diagonal.
Article: main_krylov, prop:Fcycle, exact observed-data dictionary. -/
theorem rfcFModel_eq_latest_add_diagonal (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    rfcFModel T f G r x₀ k=
      krylov.Secant.latest (crossGram (rfcFSteps T f G r x₀ k) (rfcFImages T f G r x₀ k))+
        Matrix.diagonal (rfcFValueDiagonal T f G r x₀ k) := by
  rw [rfcFModel,valueCorrectedModel_gradient]
  rw [sub_eq_add_neg,Matrix.diagonal_neg]
  rfl

/-- The real value correction in raw newest-first probed coordinates.
Article: main_krylov, prop:Fcycle. The current actual line column is divided
by its genuine nonzero squared scale; old total-step columns retain scale one. -/
def rfcFRawValueChange (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (c : Fin (k+1) → ℝ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Matrix.diagonal (fun i=>rfcFValueDiagonal T f G r x₀ k i.rev/c i^2)

/-- Reversal and the actual line-column rescaling identify the complete
native RFC-F correction with its genuine modified raw-model solve.
Article: main_krylov, prop:Fcycle, exact original-executor model input.
Proof: apply exact coordinate changes to the actual observed model; its
inverse is never replaced by a Taylor model. The coordinate hypotheses are
literal identities of real retained vectors, not asymptotic response premises. -/
theorem rfcFCorrectionStep_raw_model (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (U Z : Fin (k+1) → E) (c : Fin (k+1) → ℝ)
    (hc : ∀ i,c i≠0)
    (hS : rfcFSteps T f G r x₀ k ∘ Fin.rev=rescaleWindow U c)
    (hY : rfcFImages T f G r x₀ k ∘ Fin.rev=rescaleWindow Z c)
    (hgate : rfcFunctionGate fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)) :
    rfcFCorrectionStep T f G r x₀ k=
      combine U (modelCoefficients U (pairModel U Z+rfcFRawValueChange T f G r x₀ k c)
        (G (rfcFAnchor T f G r x₀ k))) := by
  rw [rfcFCorrectionStep_eq T f G r x₀ k hgate,rfcFModel_eq_latest_add_diagonal]
  rw [←valueModelCorrection_reverse]
  rw [hS,hY]
  exact valueModelCorrection_rescale U Z (rfcFValueDiagonal T f G r x₀ k ∘ Fin.rev) c hc _

end
end krylov.Functions
