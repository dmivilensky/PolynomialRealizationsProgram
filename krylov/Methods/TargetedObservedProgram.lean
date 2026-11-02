import krylov.Methods.TargetModelObserved
import krylov.Methods.RFCObservedProgram

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, actual primitive target-relative correction program.
Use: compile the genuine final reference-targeted full-model query and derive its true primitive coefficient domain.
Source: actual augmented observation synthesis, genuine model-coordinate invariance and proved target-relative inverse-model coefficient regularity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The actual finite primitive program makes one genuine full observed model correction relative to a fixed prior target.
Use: The actual finite primitive program makes one genuine full observed model correction relative to a fixed prior target.
Article: main_krylov, apB:prop:consist, actual primitive target-relative correction program.
Proof: Use the true augmented coefficient columns, actual latest pair model and genuine current gradient coordinate minus the fixed target. -/
def targetedObservedProgram (shape : List ℕ) (n : ℕ) (target : E) : CorrectionProgram E (n+3) :=
  .query (targetModelObservedRule (augmentedCoefficientSteps fullMemory shape n)
    (fun data => pairModel (augmentedChartSteps fullMemory shape data) (augmentedChartImages fullMemory shape data))
    (Pi.single 0 1) target) .done

/-- The actual primitive targeted program equals the genuine physical one-query latest-model tree on every true input observation array.
Use: The actual primitive targeted program equals the genuine physical one-query latest-model tree on every true input observation array.
Article: main_krylov, apB:prop:consist, actual primitive target-relative correction program.
Proof: Synthesize the actual augmented basis and invoke genuine physical model-tree coordinate invariance. -/
theorem targetedObservedProgram_tree (shape : List ℕ) (target : E) (data : Fin n → E) (d z gp : E) :
    (targetedObservedProgram shape n target).tree (Fin.cons gp (Fin.cons z (Fin.cons d data)))=
      repeatedModelTree (windowSteps ((d,z)::chartWindow fullMemory shape data))
        (windowModel ((d,z)::chartWindow fullMemory shape data)) 1 (gp-target) := by
  change CorrectionTree.query _ (fun _ => .done)=_
  rw [targetModelObservedRule_evaluate]
  simp_rw [augmentedCoefficientSteps_synthesis]
  rw [observationSynthesis_single]
  have he := augmentedChart_repeatedTree fullMemory shape data d z (gp-target) 1
  exact he.symm

/-- The genuine target-relative full-model program has C-r primitive coefficients on its true observed determinant domain.
Use: The genuine target-relative full-model program has C-r primitive coefficients on its true observed determinant domain.
Article: main_krylov, apB:prop:consist, actual primitive target-relative correction program.
Proof: Apply the actual target-relative coefficient calculus and genuine augmented model entry regularity. -/
theorem targetedObservedProgram_regular (shape : List ℕ) (target : E)
    (data : Fin (n+3) → E) (r : WithTop ℕ∞) (B : E →L[ℝ] E) (g : E)
    (hdet : (pairModel (augmentedChartSteps fullMemory shape data) (augmentedChartImages fullMemory shape data)).det≠0) :
    (targetedObservedProgram shape n target).RegularAt r B g data :=
  ⟨targetModelObservedRule_regular _ _ _ target data r (augmentedChart_model_regular fullMemory shape data r) hdet,trivial⟩
end
end krylov.Methods
