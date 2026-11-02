import krylov.Functions.NativeRFCExecution

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, faithful ordinary
RFC function/operator dictionary.
Use: identify the genuine data-only line-step correction with the existing
ordinary RFC policy on its actual search and correction segment operators.
Every actual returned gradient and the full one-query trace are retained.
Source: exact search stationarity, the segment FTC, and the proved model
column-rescaling identity. Localization is proved separately before applying
these identities to native executions.
-/

namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true line-step/secant correction equals the original direction/probe
correction for the genuine nonzero search scalar, through both actual gate branches.
Article: main_krylov, lem:cycle-transfer.
The current correction operator is arbitrary because one RFC query's chosen
movement is determined before that operator is queried. -/
theorem rfcFunctionCorrectionStep_operator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (H : History E) (A B : E →L[ℝ] E)
    (α : ℝ) (hα : α≠0)
    (hstep : rfcFunctionLineStep T f memory r x₀ H=α • rfcFunctionDirection memory H)
    (hsec : G (rfcFunctionLinePoint T f memory r x₀ H)-H.gradient=
      α • A (rfcFunctionDirection memory H))
    (hpost : G (rfcFunctionLinePoint T f memory r x₀ H)=
      searchedGradient H.gradient (rfcFunctionDirection memory H) (A (rfcFunctionDirection memory H))) :
    rfcFunctionCorrectionStep T f G memory r x₀ H=
      (runCorrections (rfcCorrection memory 1 H (A (rfcFunctionDirection memory H))) B
        (searchedGradient H.gradient (rfcFunctionDirection memory H) (A (rfcFunctionDirection memory H)))).movement := by
  classical
  by_cases hgate : rfcFunctionGate memory H
  · have hgate' : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1 := hgate
    simp only [rfcFunctionCorrectionStep,ite_eq_left hgate]
    rw [hstep,hsec,hpost]
    rw [newest_pair_model_correction_rescale _ _ _ _ α hα]
    simp only [rfcCorrection,ite_eq_left hgate',repeatedModelTree,runCorrections,add_zero,rfcFunctionDirection]
  · have hgate' : ¬(selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) := hgate
    simp only [rfcFunctionCorrectionStep,ite_eq_right hgate,rfcCorrection,ite_eq_right hgate',runCorrections]

/-- The actual correction phase has exactly the native ordinary RFC gradient
and complete real query trace, once its true correction secant is identified.
Article: main_krylov, lem:cycle-transfer. -/
theorem rfcFunction_correction_phase (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (H : History E) (A B : E →L[ℝ] E)
    (α : ℝ) (hα : α≠0)
    (hstep : rfcFunctionLineStep T f memory r x₀ H=α • rfcFunctionDirection memory H)
    (hsec : G (rfcFunctionLinePoint T f memory r x₀ H)-H.gradient=
      α • A (rfcFunctionDirection memory H))
    (hpost : G (rfcFunctionLinePoint T f memory r x₀ H)=
      searchedGradient H.gradient (rfcFunctionDirection memory H) (A (rfcFunctionDirection memory H)))
    (hquery : G (rfcFunctionLinePoint T f memory r x₀ H+rfcFunctionCorrectionStep T f G memory r x₀ H)=
      G (rfcFunctionLinePoint T f memory r x₀ H)+B (rfcFunctionCorrectionStep T f G memory r x₀ H)) :
    runCorrections (rfcCorrection memory 1 H (A (rfcFunctionDirection memory H))) B
      (searchedGradient H.gradient (rfcFunctionDirection memory H) (A (rfcFunctionDirection memory H)))=
      ⟨rfcFunctionCorrectionStep T f G memory r x₀ H,
        G (rfcFunctionLinePoint T f memory r x₀ H+rfcFunctionCorrectionStep T f G memory r x₀ H),
        (rfcFunctionRecord T f G memory r x₀ H).corrections⟩ := by
  classical
  have hu := rfcFunctionCorrectionStep_operator T f G memory r x₀ H A B α hα hstep hsec hpost
  by_cases hgate : rfcFunctionGate memory H
  · have hgate' : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1 := hgate
    simp only [rfcCorrection,ite_eq_left hgate',repeatedModelTree,runCorrections,add_zero,
      rfcFunctionRecord,ite_eq_left hgate] at hu ⊢
    rw [← hu,← hpost,← hquery]
  · have hgate' : ¬(selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) := hgate
    simp only [rfcCorrection,ite_eq_right hgate',runCorrections,rfcFunctionRecord,ite_eq_right hgate] at hu ⊢
    rw [hu,add_zero]
    exact congrArg (fun g : E => (⟨0,g,[]⟩ : CorrectionResult E)) hpost.symm

/-- Every genuine ordinary RFC iteration agrees exactly with its existing
operator-policy execution on true segment operators.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer.
Proof: the actual line scalar reconstructs its measured probe; exact model
rescaling identifies the physical correction; the true correction secant
identifies the returned gradient and the entire actual trace. -/
theorem rfcFunctionRecord_operator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (H : History E) (A B : E →L[ℝ] E)
    (hd : rfcFunctionDirection memory H≠0)
    (hα : lineLength H.gradient (rfcFunctionDirection memory H) (A (rfcFunctionDirection memory H))≠0)
    (hstep : rfcFunctionLineStep T f memory r x₀ H=
      lineLength H.gradient (rfcFunctionDirection memory H) (A (rfcFunctionDirection memory H)) • rfcFunctionDirection memory H)
    (hpost : G (rfcFunctionLinePoint T f memory r x₀ H)=
      searchedGradient H.gradient (rfcFunctionDirection memory H) (A (rfcFunctionDirection memory H)))
    (hquery : G (rfcFunctionLinePoint T f memory r x₀ H+rfcFunctionCorrectionStep T f G memory r x₀ H)=
      G (rfcFunctionLinePoint T f memory r x₀ H)+B (rfcFunctionCorrectionStep T f G memory r x₀ H)) :
    methodAdvance (rfcMethod memory 1) A B H=
      ⟨H.initial,rfcFunctionRecord T f G memory r x₀ H::H.records⟩ := by
  let d := rfcFunctionDirection memory H
  let α := lineLength H.gradient d (A d)
  have hsec : G (rfcFunctionLinePoint T f memory r x₀ H)-H.gradient=α • A d := by
    rw [hpost,searchedGradient]
    abel
  have hprobe : (rfcFunctionRecord T f G memory r x₀ H).probe=A d := by
    change (observedLineParameter d (rfcFunctionLineStep T f memory r x₀ H))⁻¹ •
      (G (rfcFunctionLinePoint T f memory r x₀ H)-H.gradient)=_
    rw [hstep,observedLineParameter_smul d α hd,hsec,smul_smul,inv_mul_cancel₀ hα,one_smul]
  have hphase := rfcFunction_correction_phase T f G memory r x₀ H A B α hα hstep hsec hpost hquery
  change runCorrections ((rfcMethod memory 1).correction H (A ((rfcMethod memory 1).direction H))) B
    (searchedGradient H.gradient ((rfcMethod memory 1).direction H)
      (A ((rfcMethod memory 1).direction H)))=_ at hphase
  change (⟨H.initial,(⟨d,A d,α • d+_,_,_⟩ : IterationRecord E)::H.records⟩ : History E)=_
  rw [hphase]
  congr 2
  simp only [rfcFunctionRecord,IterationRecord.mk.injEq]
  exact ⟨rfl,hprobe.symm,
    congrArg (fun s => s+rfcFunctionCorrectionStep T f G memory r x₀ H) hstep.symm,trivial,trivial⟩

end
end krylov.Functions
