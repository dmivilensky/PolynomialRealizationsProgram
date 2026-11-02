import krylov.Nonlinear.RFCSFunction
import krylov.Methods.RFCSHomogeneous

/-!
Article: main_krylov, thm:RFCS, actual nonlinear search-field dictionary.
Use: Expose the genuine nonlinear predicted search length, line displacement
and physical correction, and identify them from complete actual operator
prefix equality including all true probe and recorded-step observations.
Source: the original nonlinear executor and proved full measured RFC-S history.
-/

namespace krylov.Nonlinear
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine predicted search length computed from the actual current gradient and true finite probe recorded by the nonlinear RFC-S executor.
Use: Keep the source relative probe error tied to the actual nonlinear measured quotient.
Article: main_krylov, thm:RFCS, true nonlinear search and correction fields.
-/
def rfcSFunctionAlpha (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ) (i : ℕ) : ℝ :=
  let H := rfcSFunctionRun memory G x₀ h i
  let R := rfcSFunctionRecord memory G x₀ (h i) H
  lineLength H.gradient R.direction R.probe

/-- The actual secant-predicted line displacement of the genuine nonlinear RFC-S iteration.
Use: Compare the real nonlinear line/probe endpoints and the original quadratic reference step.
Article: main_krylov, thm:RFCS, true nonlinear search and correction fields.
-/
def rfcSFunctionLineStep (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ) (i : ℕ) : E :=
  rfcSFunctionAlpha memory G x₀ h i •
    (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).direction

/-- The actual physical model correction in the nonlinear RFC-S total evaluated displacement.
Use: Retain the genuine correction contribution in the final averaged-Hessian mismatch estimate.
Article: main_krylov, thm:RFCS, true nonlinear search and correction fields.
-/
def rfcSFunctionCorrection (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ) (i : ℕ) : E :=
  (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step-
    rfcSFunctionLineStep memory G x₀ h i

/-- Exact complete measured-prefix equality identifies every genuine nonlinear RFC-S direction, probe, total step, search length, predicted line displacement and physical correction with the original actual operator fields.
Use: Transfer proved compact source search/correction estimates to the real nonlinear execution without assuming field identities.
Article: main_krylov, thm:RFCS, true nonlinear search and correction fields.
Proof: Read the actual direction from the common measured prefix, the true probe from the equal newest record and the real total step from the proved actual pair transcript. The actual scalar search and line/correction formulas then agree exactly.
-/
theorem rfcSFunctionRecord_operator_fields (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ)
    (Ap A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ)
    (hpre : rfcSFunctionRun memory G x₀ h i=rfcSRun memory Ap A B g i)
    (hsucc : rfcSFunctionRun memory G x₀ h (i+1)=rfcSRun memory Ap A B g (i+1)) :
    let R := rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)
    R.direction=rfcSDirection memory Ap A B g i ∧ R.probe=Ap i (rfcSDirection memory Ap A B g i) ∧
      R.step=rfcSStep memory Ap A B g i ∧
      rfcSFunctionAlpha memory G x₀ h i=lineLength (rfcSGradient memory Ap A B g i)
        (rfcSDirection memory Ap A B g i) (Ap i (rfcSDirection memory Ap A B g i)) ∧
      rfcSFunctionLineStep memory G x₀ h i=rfcSLineStep memory Ap A B g i ∧
      rfcSFunctionCorrection memory G x₀ h i=rfcSStep memory Ap A B g i-rfcSLineStep memory Ap A B g i := by
  dsimp only
  have hd : (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).direction=
      rfcSDirection memory Ap A B g i := by
    rw [rfcSFunctionRecord_direction,hpre]
    rfl
  have hprobe : ((rfcSRun memory Ap A B g (i+1)).records.map IterationRecord.probe).headD 0=
      Ap i (rfcSDirection memory Ap A B g i) := by
    rw [rfcSRun]
    unfold rfcSAdvance
    dsimp only
    split <;> rfl
  have hp := congrArg (fun H : History E => (H.records.map IterationRecord.probe).headD 0) hsucc
  rw [hprobe] at hp
  change (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).probe=_ at hp
  have ht := congrArg (fun H : History E => (H.pairs.headD (0,0)).1) hsucc
  rw [rfcSRun_pairs] at ht
  change (rfcSFunctionRecord memory G x₀ (h i) (rfcSFunctionRun memory G x₀ h i)).step=
    rfcSStep memory Ap A B g i at ht
  have hg : (rfcSFunctionRun memory G x₀ h i).gradient=rfcSGradient memory Ap A B g i :=
    congrArg History.gradient hpre
  have ha : rfcSFunctionAlpha memory G x₀ h i=lineLength (rfcSGradient memory Ap A B g i)
      (rfcSDirection memory Ap A B g i) (Ap i (rfcSDirection memory Ap A B g i)) := by
    unfold rfcSFunctionAlpha
    dsimp only
    rw [hg,hd,hp]
  have hl : rfcSFunctionLineStep memory G x₀ h i=rfcSLineStep memory Ap A B g i := by
    rw [rfcSFunctionLineStep,ha,hd]
    rfl
  refine ⟨hd,hp,ht,ha,hl,?_⟩
  rw [rfcSFunctionCorrection,ht,hl]

/-- The true nonlinear RFC-S search length agrees with its normalized actual operator field, while its genuine line and correction displacements scale by the actual positive cycle size.
Use: Apply compact normalized source search/correction estimates directly to real nonlinear observations.
Article: main_krylov, thm:RFCS, actual scaled nonlinear search-field dictionary.
Proof: The proved genuine complete-record field dictionary identifies the actual observations. Exact real RFC-S homogeneity preserves the scalar search length and scales both actual line and full recorded step; their true difference scales too.
-/
theorem rfcSFunction_scaled_operator_fields (memory : ℕ → ℕ) (G : E → E) (x₀ : E) (h : ℕ → ℝ)
    (Ap A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (i : ℕ)
    (hpre : rfcSFunctionRun memory G x₀ h i=rfcSRun memory Ap A B (c • g) i)
    (hsucc : rfcSFunctionRun memory G x₀ h (i+1)=rfcSRun memory Ap A B (c • g) (i+1)) :
    rfcSFunctionAlpha memory G x₀ h i=lineLength (rfcSGradient memory Ap A B g i)
      (rfcSDirection memory Ap A B g i) (Ap i (rfcSDirection memory Ap A B g i)) ∧
      rfcSFunctionLineStep memory G x₀ h i=c • rfcSLineStep memory Ap A B g i ∧
      rfcSFunctionCorrection memory G x₀ h i=c • (rfcSStep memory Ap A B g i-rfcSLineStep memory Ap A B g i) := by
  obtain ⟨_,_,_,ha,hl,hcor⟩ := rfcSFunctionRecord_operator_fields memory G x₀ h Ap A B (c • g) i hpre hsucc
  have hg := (rfcS_scalar memory Ap A B g c hc i).1
  have hs := (rfcS_scalar memory Ap A B g c hc (i+1)).2 i (Nat.lt_succ_self i)
  refine ⟨?_,?_,?_⟩
  · rw [ha,hg,hs.1,map_smul,lineLength_scalar _ _ _ c hc]
  · rw [hl,hs.2.1]
  · rw [hcor,hs.2.2.1,hs.2.1,smul_sub]

end
end krylov.Nonlinear
