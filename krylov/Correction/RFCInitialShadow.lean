import krylov.Correction.RFCInitialReference
import krylov.Correction.GatedRFCComparison

/-!
Article: main_krylov, thm:UCq, exact small-dimensional shadow bootstrap.
Use: Transfer the real first empty-window history and the next accepted
correction to ordinary RFC without an unnecessary first spectral-test premise.
Source: the existing actual empty-window RFC executor and original spectral
gate branch definition, preserving every true record and query observation.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine first full gated-RFC history equals ordinary RFC for every actual source and threshold because its real old window is empty.
Use: Start the low-dimensional true shadow comparison before any nonempty model query.
Article: main_krylov, thm:UCq.
Proof: The actual empty-window ordinary correction tree is done. Both real spectral branches therefore return that same empty tree, giving identical complete first records under the common search.
-/
theorem gated_initial_history_eq_rfc (γ : ℝ) (A B : ℕ → E →L[ℝ] E) (g : E) :
    methodRun (gatedMethod fullMemory γ) A B g 1=methodRun (rfcMethod fullMemory 1) A B g 1 := by
  have hrc z : rfcCorrection fullMemory 1 (⟨g,[]⟩ : History E) z=.done := by
    simp [rfcCorrection,selectedWindow,fullMemory]
  have hgc z : gatedCorrection fullMemory γ (⟨g,[]⟩ : History E) z=.done := by
    unfold gatedCorrection
    dsimp only
    split
    · exact hrc z
    · rfl
  simp [methodRun,methodAdvance,gatedMethod,rfcMethod,retainedMethod,hgc,hrc,runCorrections]

/-- One genuine accepted spectral test extends actual complete ordinary/gated history equality through the next original iteration.
Use: Bootstrap the true small-dimensional prefix using only its actual current measured decision.
Article: main_krylov, thm:UCq.
Proof: The real passed test makes the original gated correction tree exactly the ordinary RFC tree on their shared actual history. Execute that same tree with its common real probe, line and correction operator; every true next record field agrees.
-/
theorem gated_rfc_next_history_eq_of_gate (γ : ℝ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (heq : methodRun (gatedMethod fullMemory γ) A B g k=methodRun (rfcMethod fullMemory 1) A B g k)
    (hgate :
      let H := methodRun (gatedMethod fullMemory γ) A B g k
      let W := selectedWindow fullMemory H
      let d := windowDirection W H.gradient
      spectralGate γ ((d,A k d)::W)) :
    methodRun (gatedMethod fullMemory γ) A B g (k+1)=methodRun (rfcMethod fullMemory 1) A B g (k+1) := by
  have hc : gatedCorrection fullMemory γ (methodRun (gatedMethod fullMemory γ) A B g k)
      (A k ((gatedMethod fullMemory γ).direction (methodRun (gatedMethod fullMemory γ) A B g k)))=
      rfcCorrection fullMemory 1 (methodRun (gatedMethod fullMemory γ) A B g k)
        (A k ((gatedMethod fullMemory γ).direction (methodRun (gatedMethod fullMemory γ) A B g k))) := by
    unfold gatedCorrection
    exact ite_eq_left hgate
  rw [methodRun,methodRun,← heq]
  unfold methodAdvance
  dsimp only [gatedMethod,rfcMethod,retainedMethod] at hc ⊢
  rw [hc]

end
end krylov.Correction
