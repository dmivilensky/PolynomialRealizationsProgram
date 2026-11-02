import krylov.Functions.NativeRFCOperators
import krylov.Functions.RFCOperatorQueries

/-!
Article: main_krylov, lem:cycle-transfer, noncircular ordinary RFC correction control.
Use: obtain the actual query displacement from finite normalized inputs before
requiring its endpoint to lie in the Hessian domain. The current correction
operator can be replaced by the reference operator during this estimate.
Source: exact native/operator dictionary, nonanticipation, compact analytic
reference stability and actual degree-one homogeneity.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A true native search in finite reference coordinates has a controlled
correction before its actual correction operator is available.
Article: main_krylov, lem:cycle-transfer, ordinary RFC bootstrap.
The two reference-tube premises are precisely the independently proved
compact field/domain conclusions; the actual correction endpoint and its
operator do not occur in the hypotheses. -/
theorem rfcFunctionCorrectionStep_finite_bound
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (r : ℝ) (x₀ : E) (D : History E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (ε C η : ℝ) (hε : 0<ε) (k : ℕ)
    (hhistory : D=methodRun (rfcMethod fullMemory 1) A B (ε • g) k)
    (hstep : rfcFunctionLineStep T f fullMemory r x₀ D=
      lineLength D.gradient (rfcFunctionDirection fullMemory D) (A k (rfcFunctionDirection fullMemory D)) • rfcFunctionDirection fullMemory D)
    (hpost : G (rfcFunctionLinePoint T f fullMemory r x₀ D)=
      searchedGradient D.gradient (rfcFunctionDirection fullMemory D) (A k (rfcFunctionDirection fullMemory D)))
    (hdom : (rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g k)≠0 ∧
      lineLength (probedGradient (rfcMethod fullMemory 1) A B g k)
        ((rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g k))
        (A k ((rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g k)))≠0)
    (hbound : ‖rfcOperatorCorrection A B g k‖≤C*η) :
    rfcFunctionDirection fullMemory D≠0 ∧
      lineLength D.gradient (rfcFunctionDirection fullMemory D) (A k (rfcFunctionDirection fullMemory D))≠0 ∧
      ‖rfcFunctionCorrectionStep T f G fullMemory r x₀ D‖≤ε*C*η := by
  have hg := (rfc_scalar fullMemory 1 A B g ε hε.ne' k).1
  have hd := (rfc_scalar fullMemory 1 A B g ε hε.ne' (k+1)).2 k (by omega)
  have hds : rfcFunctionDirection fullMemory D=ε •
      (rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g k) := by
    rw [hhistory]
    exact hd.1
  have hα : lineLength D.gradient (rfcFunctionDirection fullMemory D)
      (A k (rfcFunctionDirection fullMemory D))≠0 := by
    rw [hhistory]
    change lineLength (probedGradient _ _ _ _ _) ((rfcMethod fullMemory 1).direction _)
      (A k ((rfcMethod fullMemory 1).direction _))≠0
    rw [hg,hd.1,map_smul,lineLength_scalar _ _ _ ε hε.ne']
    exact hdom.2
  refine ⟨hds ▸ smul_ne_zero hε.ne' hdom.1,hα,?_⟩
  have hsec : G (rfcFunctionLinePoint T f fullMemory r x₀ D)-D.gradient=
      lineLength D.gradient (rfcFunctionDirection fullMemory D) (A k (rfcFunctionDirection fullMemory D)) •
        A k (rfcFunctionDirection fullMemory D) := by
    rw [hpost,searchedGradient]
    abel
  have hu := rfcFunctionCorrectionStep_operator T f G fullMemory r x₀ D (A k) (B k)
    _ hα hstep hsec hpost
  have hup : rfcFunctionCorrectionStep T f G fullMemory r x₀ D=rfcOperatorCorrection A B (ε • g) k := by
    rw [rfcOperatorCorrection_eq_phase]
    rw [hu,hhistory]
    rfl
  rw [hup,rfcOperatorCorrection_scalar A B g ε hε.ne',norm_smul,Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left hbound hε.le).trans_eq (by ring)

end
end krylov.Functions
