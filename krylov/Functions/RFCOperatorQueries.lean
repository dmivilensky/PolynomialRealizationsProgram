import krylov.Functions.RFCReferenceFields
import krylov.Functions.NativeRFCEmbedding

/-!
Article: main_krylov, lem:cycle-transfer, ordinary RFC bootstrap oracle fields.
Use: expose the actual one-query correction before querying its current
operator, and transport finite normalized oracle coordinates faithfully.
Source: true one-query RFC execution and proved trajectory homogeneity.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Subtracting the real line step extracts precisely the true RFC correction.
Article: main_krylov, alg:fc. -/
theorem rfcOperatorCorrection_eq_phase (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) :
    rfcOperatorCorrection A B g i=(probedPhase (rfcMethod fullMemory 1) A B g i).movement := by
  unfold rfcOperatorCorrection rfcOperatorLineStep probedStep
  dsimp only
  abel

/-- The movement of one genuine RFC query cannot depend on that query's as-yet
unobserved operator. Article: main_krylov, def:classes, nonanticipation. -/
theorem rfcCorrection_one_movement_operator (memory : ℕ → ℕ) (H : History E)
    (z g : E) (B C : E →L[ℝ] E) :
    (runCorrections (rfcCorrection memory 1 H z) B g).movement=
      (runCorrections (rfcCorrection memory 1 H z) C g).movement := by
  classical
  by_cases hg : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1
  · simp only [rfcCorrection,ite_eq_left hg,repeatedModelTree,runCorrections]
  · simp only [rfcCorrection,ite_eq_right hg,runCorrections]

/-- Every true RFC correction query is degree one in its actual initial
observation, with all search and correction operators fixed.
Article: main_krylov, lem:U(c,d). -/
theorem rfcOperatorCorrection_scalar (A B : ℕ → E →L[ℝ] E) (g : E)
    (c : ℝ) (hc : c≠0) (i : ℕ) :
    rfcOperatorCorrection A B (c • g) i=c • rfcOperatorCorrection A B g i := by
  have h := rfc_scalar fullMemory 1 A B g c hc (i+1)
  have hg := (rfc_scalar fullMemory 1 A B g c hc i).1
  have hd := (h.2 i (by omega)).1
  have hs := (h.2 i (by omega)).2.1
  have hl : rfcOperatorLineStep A B (c • g) i=c • rfcOperatorLineStep A B g i := by
    change lineLength (probedGradient _ _ _ _ i) _ _ • _=_
    rw [hg,hd,map_smul,lineLength_scalar _ _ _ c hc,smul_comm]
    rfl
  rw [rfcOperatorCorrection,hs,hl,←smul_sub]
  rfl

/-- Finite input coordinates determine the complete ordinary RFC history
through exactly the already observed prefix. Article: main_krylov, lem:cycle-transfer. -/
theorem rfcFinite_history (Q : E →L[ℝ] E) (N k : ℕ)
    (A B : ℕ → E →L[ℝ] E) (Θ Ξ : Fin N → E →L[ℝ] E) (g : E)
    (hA : ∀ j<k, A j=fcFiniteOperatorPath Q N Θ j)
    (hB : ∀ j<k, B j=fcFiniteOperatorPath Q N Ξ j) :
    methodRun (rfcMethod fullMemory 1) A B g k=
      methodRun (rfcMethod fullMemory 1) (fcFiniteOperatorPath Q N Θ) (fcFiniteOperatorPath Q N Ξ) g k :=
  methodRun_congr_prefix _ _ _ _ _ _ _ hA hB

end
end krylov.Functions
