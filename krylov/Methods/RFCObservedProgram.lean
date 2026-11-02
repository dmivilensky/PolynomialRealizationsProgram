import krylov.Methods.ModelObservedProgram
import krylov.Methods.RFCObservedCharts

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, genuine primitive RFC correction programs.
Use: compile each actual finite RFC repeated-query phase and derive its
primitive coefficient regularity from the true augmented model domain.
Source: actual original observation synthesis, real fixed-dimensional RFC
model charts and the proved genuine repeated model-program executor.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The genuine finite primitive observed-coefficient RFC repeated correction program.
Use: The genuine finite primitive observed-coefficient RFC repeated correction program.
Article: main_krylov, def:classes and cor:lm, genuine primitive RFC correction programs.
Proof: Use the actual augmented retained basis coefficients, its true observed latest model and the actual incoming gradient coordinate. -/
def rfcObservedProgram (memory : ℕ → ℕ) (shape : List ℕ) (n count : ℕ) : CorrectionProgram E (n+3) :=
  repeatedObservedModel count (augmentedCoefficientSteps memory shape n)
    (fun data => pairModel (augmentedChartSteps memory shape data) (augmentedChartImages memory shape data))
    (Pi.single 0 1)

/-- The actual primitive RFC program is exactly the genuine physical repeated RFC tree on every possible true continuation answer.
Use: The actual primitive RFC program is exactly the genuine physical repeated RFC tree on every possible true continuation answer.
Article: main_krylov, def:classes and cor:lm, genuine primitive RFC correction programs.
Proof: Apply the actual repeated-program synthesis identity, identify the genuine basis and current gradient, and reuse true physical model-tree coordinate invariance. -/
theorem rfcObservedProgram_tree (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (d z gp : E) (count : ℕ) :
    (rfcObservedProgram memory shape n count).tree (Fin.cons gp (Fin.cons z (Fin.cons d data)))=
    repeatedModelTree (windowSteps ((d,z)::chartWindow memory shape data))
      (windowModel ((d,z)::chartWindow memory shape data)) count gp := by
  rw [rfcObservedProgram,repeatedObservedModel_tree]
  simp_rw [augmentedCoefficientSteps_synthesis]
  rw [observationSynthesis_single]
  exact (augmentedChart_repeatedTree memory shape data d z gp count).symm

/-- The real finite RFC correction program has C-r primitive coefficients at every true nonsingular augmented observed model.
Use: The real finite RFC correction program has C-r primitive coefficients at every true nonsingular augmented observed model.
Article: main_krylov, def:classes and cor:lm, genuine primitive RFC correction programs.
Proof: Each actual augmented latest-model entry is C-r, and the genuine repeated-program coefficient theorem preserves precisely its true inverse domain. -/
theorem rfcObservedProgram_regular (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin (n+3) → E)
    (count : ℕ) (r : WithTop ℕ∞) (B : E →L[ℝ] E) (g : E)
    (hdet : (pairModel (augmentedChartSteps memory shape data) (augmentedChartImages memory shape data)).det≠0) :
    (rfcObservedProgram memory shape n count).RegularAt r B g data :=
  repeatedObservedModel_regular _ _ _ count data r B g (augmentedChart_model_regular memory shape data r) hdet
end
end krylov.Methods
