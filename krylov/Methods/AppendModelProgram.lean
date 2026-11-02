import krylov.Methods.CorrectionFollow
import krylov.Methods.ModelObservedProgram

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), actual appended latest-model primitive program.
Use: append one genuine fixed-model correction to any true finite
primitive observed correction program, preserving the real original
model and basis through all actual intermediate observations.
Source: genuine finite observation coefficient zero extension and the
proved actual model-program synthesis and correction-tree continuation.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual primitive finite correction program followed by one genuine latest-model query with its true returned gradient.
Use: An actual primitive finite correction program followed by one genuine latest-model query with its true returned gradient.
Article: main_krylov, thm:select and apB:lem:mu(a), actual appended latest-model primitive program.
Proof: Retain each real original query; zero-extend the genuine fixed model basis through its actual new observations and read the true incoming gradient at termination. -/
def CorrectionProgram.appendModel : {n : ℕ} → CorrectionProgram E n →
    (ι → Fin n → ℝ) → ((Fin n → E) → Matrix ι ι ℝ) → (Fin n → ℝ) → CorrectionProgram E n
  | _,.done,s,H,c => repeatedObservedModel 1 s H c
  | _,.query rule next,s,H,_ => .query rule (next.appendModel (fun i => liftCoefficientsTwo (s i))
      (fun data => H (Fin.tail (Fin.tail data))) (Pi.single 0 1))

/-- The actual appended primitive coefficient program compiles exactly to the genuine original correction tree followed by one real fixed-model correction on its true returned gradient.
Use: The actual appended primitive coefficient program compiles exactly to the genuine original correction tree followed by one real fixed-model correction on its true returned gradient.
Article: main_krylov, thm:select and apB:lem:mu(a), actual appended latest-model primitive program.
Proof: Induct through genuine original queries. Actual zero extension preserves the real original model and basis while the true newly returned gradient becomes the actual current head observation. -/
theorem CorrectionProgram.appendModel_tree {n : ℕ} (P : CorrectionProgram E n)
    (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ) (c : Fin n → ℝ) (data : Fin n → E) :
    (P.appendModel s H c).tree data=(P.tree data).follow
      (fun gnew => repeatedModelTree (fun i => observationSynthesis data (s i)) (H data) 1 gnew)
      (observationSynthesis data c) := by
  -- Preserve the genuine original model and fixed basis as actual new gradient and query observations are prepended.
  induction P with
  | done =>
    rw [CorrectionProgram.appendModel,repeatedObservedModel_tree]
    rfl
  | @query n rule next ih =>
    change CorrectionTree.query (rule.evaluate data) _=CorrectionTree.query (rule.evaluate data) _
    congr 1
    funext gnew
    rw [ih]
    simp only [observationSynthesis_lift_two,Fin.tail_cons,observationSynthesis_single]
    rfl

/-- Appending the genuine model query preserves actual primitive coefficient regularity on the true original program and model determinant domains.
Use: Appending the genuine model query preserves actual primitive coefficient regularity on the true original program and model determinant domains.
Article: main_krylov, thm:select and apB:lem:mu(a), actual appended latest-model primitive program.
Proof: Induct through the actual finite original program and its true reached gradients. The genuine original model domain survives real observation zero extension, and the true terminal query has actual smooth inverse-model coefficients. -/
theorem CorrectionProgram.appendModel_regular {n : ℕ} (P : CorrectionProgram E n)
    (s : ι → Fin n → ℝ) (H : (Fin n → E) → Matrix ι ι ℝ) (c : Fin n → ℝ)
    (data : Fin n → E) (r : WithTop ℕ∞) (B : E →L[ℝ] E) (g : E)
    (hP : P.RegularAt r B g data)
    (hH : ∀ i j, ContDiffAt ℝ r (fun p => H p i j) data) (hdet : (H data).det≠0) :
    (P.appendModel s H c).RegularAt r B g data := by
  -- Retain the true reached gradient at each actual original query while transferring the genuine unchanged model inverse domain.
  induction P generalizing g with
  | done => exact repeatedObservedModel_regular s H c 1 data r B g hH hdet
  | @query n rule next ih =>
    refine ⟨hP.1,?_⟩
    let nextData : Fin (n+2) → E := Fin.cons (g+B (rule.evaluate data)) (Fin.cons (rule.evaluate data) data)
    apply ih (fun i => liftCoefficientsTwo (s i)) (fun data : Fin (n+2) → E => H (Fin.tail (Fin.tail data)))
      (Pi.single 0 1) nextData (g+B (rule.evaluate data)) hP.2
    · intro i j
      exact (hH i j).comp nextData (contDiffAt_pi.mpr fun l : Fin n => contDiffAt_pi.mp
        (show ContDiffAt ℝ r (fun p : Fin (n+2) → E => p) nextData from contDiffAt_id) l.succ.succ)
    · exact hdet
end
end krylov.Methods
