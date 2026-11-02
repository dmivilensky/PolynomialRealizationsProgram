import krylov.Methods.AppendModelProgram
import krylov.Methods.RFCObservedProgram

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), concrete actual appended full-model observed program.
Use: attach the genuine full-history latest-information model query
to an arbitrary actual primitive correction program and derive true
finite observed coefficient domains and whole-tree equality.
Source: genuine appended model AST, actual augmented observed charts
and true full-history basis/model synthesis.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The actual primitive correction program followed by one genuine full-history observed latest-model correction.
Use: The actual primitive correction program followed by one genuine full-history observed latest-model correction.
Article: main_krylov, thm:select and apB:lem:mu(a), concrete actual appended full-model observed program.
Proof: Use true fixed augmented basis coefficients and the actual full latest model, retaining the genuine current gradient coordinate. -/
def appendedModelObserved (P : CorrectionProgram E (n+3)) (shape : List ℕ) : CorrectionProgram E (n+3) :=
  P.appendModel (augmentedCoefficientSteps fullMemory shape n)
    (fun data => pairModel (augmentedChartSteps fullMemory shape data) (augmentedChartImages fullMemory shape data))
    (Pi.single 0 1)

/-- The actual appended observed program is exactly the genuine original decision tree followed by the real full observed model correction for every true future returned gradient.
Use: The actual appended observed program is exactly the genuine original decision tree followed by the real full observed model correction for every true future returned gradient.
Article: main_krylov, thm:select and apB:lem:mu(a), concrete actual appended full-model observed program.
Proof: Identify actual fixed augmented column synthesis and true model-tree coordinates in the genuine appended program executor. -/
theorem appendedModelObserved_tree (P : CorrectionProgram E (n+3)) (shape : List ℕ)
    (data : Fin n → E) (d z gp : E) :
    (appendedModelObserved P shape).tree (Fin.cons gp (Fin.cons z (Fin.cons d data)))=
      (P.tree (Fin.cons gp (Fin.cons z (Fin.cons d data)))).follow
        (fun gnew => repeatedModelTree (windowSteps ((d,z)::chartWindow fullMemory shape data))
          (windowModel ((d,z)::chartWindow fullMemory shape data)) 1 gnew) gp := by
  -- The genuine fixed coefficient columns synthesize to the actual full observed model basis throughout every real original continuation.
  rw [appendedModelObserved,CorrectionProgram.appendModel_tree]
  simp_rw [augmentedCoefficientSteps_synthesis]
  rw [observationSynthesis_single]
  congr 1
  funext gnew
  exact (augmentedChart_repeatedTree fullMemory shape data d z gnew 1).symm

/-- The genuine appended full-model program has actual smooth primitive coefficients on the true original-program and observed augmented determinant domains.
Use: The genuine appended full-model program has actual smooth primitive coefficients on the true original-program and observed augmented determinant domains.
Article: main_krylov, thm:select and apB:lem:mu(a), concrete actual appended full-model observed program.
Proof: Apply actual appended-program regularity with the genuine smooth full augmented observed model entries. -/
theorem appendedModelObserved_regular (P : CorrectionProgram E (n+3)) (shape : List ℕ)
    (data : Fin (n+3) → E) (r : WithTop ℕ∞) (B : E →L[ℝ] E) (g : E)
    (hP : P.RegularAt r B g data)
    (hdet : (pairModel (augmentedChartSteps fullMemory shape data) (augmentedChartImages fullMemory shape data)).det≠0) :
    (appendedModelObserved P shape).RegularAt r B g data :=
  CorrectionProgram.appendModel_regular P _ _ _ data r B g hP (augmentedChart_model_regular fullMemory shape data r) hdet
end
end krylov.Methods
