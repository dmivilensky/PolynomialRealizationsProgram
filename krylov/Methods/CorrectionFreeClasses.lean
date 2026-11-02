import krylov.Methods.NonlinearCGSmoothClass
import krylov.Methods.LBFGSSmoothClass
import krylov.Methods.FCSmoothClass
import krylov.Methods.CorrectionCount
import krylov.Methods.CorrectionFree

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Use: link the genuine smooth HS, HZ, BFGS/L-BFGS and FC implementations
to the actual correction-free source subclass and its true inclusion
in the at-most-one-correction class.
Source: actual raw correction decisions and the existing genuine
correction-free and one-correction source predicates.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual nonlinear CG scalar recurrence makes no correction query on any real observed history.
Use: Every actual nonlinear CG scalar recurrence makes no correction query on any real observed history.
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Proof: Its true correction tree is empty by definition. -/
theorem nonlinearCGMethod_correctionFree (coefficient : E → E → E → ℝ) :
    CorrectionFree (nonlinearCGMethod coefficient) := fun _ _ => rfl

/-- Every actual BFGS/L-BFGS two-loop policy makes no correction query on any real observed history.
Use: Every actual BFGS/L-BFGS two-loop policy makes no correction query on any real observed history.
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Proof: Its genuine correction tree is empty by definition. -/
theorem lbfgsMethod_correctionFree (memory : ℕ → ℕ) (scale : History E → ℝ) :
    CorrectionFree (lbfgsMethod memory scale) := fun _ _ => rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The genuine correction-free source class is contained in the actual at-most-one-correction subclass.
Use: The genuine correction-free source class is contained in the actual at-most-one-correction subclass.
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Proof: Every real correction tree terminates before its first query. -/
theorem correctionFree_oneCorrection (m : ProbedMethod E) (hm : CorrectionFree m) : OneCorrectionMethod m := by
  intro H z
  rw [hm]
  trivial

/-- The actual primitive smooth HS class member belongs to the genuine correction-free subclass.
Use: The actual primitive smooth HS class member belongs to the genuine correction-free subclass.
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Proof: Use its actual nonlinear CG correction decision. -/
theorem smoothHSClass_correctionFree : CorrectionFree (smoothHSClass (E := E)).policy :=
  nonlinearCGMethod_correctionFree _

/-- The actual primitive smooth HZ class member belongs to the genuine correction-free subclass.
Use: The actual primitive smooth HZ class member belongs to the genuine correction-free subclass.
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Proof: Use the true nonlinear CG empty correction tree. -/
theorem smoothHZClass_correctionFree : CorrectionFree (smoothHZClass (E := E)).policy :=
  nonlinearCGMethod_correctionFree _

/-- Every actual primitive smooth scalar-initialized BFGS/L-BFGS class member belongs to the genuine correction-free subclass.
Use: Every actual primitive smooth scalar-initialized BFGS/L-BFGS class member belongs to the genuine correction-free subclass.
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Proof: Use the actual two-loop policy empty correction decision. -/
theorem smoothLBFGSClass_correctionFree (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (c : ℝ) (hc : 0<c) : CorrectionFree (smoothLBFGSClass (E := E) memory hm c hc).policy :=
  lbfgsMethod_correctionFree _ _

/-- Every actual primitive smooth retained-window FC class member belongs to the genuine correction-free subclass.
Use: Every actual primitive smooth retained-window FC class member belongs to the genuine correction-free subclass.
Article: main_krylov, def:classes and s3:cor:qn, actual named correction-free smooth methods.
Proof: The real FC correction tree is empty. -/
theorem smoothFCClass_correctionFree (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) :
    CorrectionFree (smoothFCClass (E := E) memory hm).policy := fun _ _ => rfl
end
end krylov.Methods
