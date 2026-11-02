import krylov.Methods.ExecutedProbed
import krylov.Methods.WindowCoordinates
import krylov.Methods.InformationSpan

/-!
Article: main_krylov, alg:fc, lem:U(d) and lem:projected-residual, real RFC coefficient coordinates.
Use: identify an accepted actual RFC correction decision tree exactly with its
fixed current-plus-retained-age coefficient solve before applying order estimates.
Source: genuine recorded-pair coordinates and the proved full decision-tree reindexing invariance.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every accepted actual RFC correction tree is exactly its fixed finite-coordinate real model-query tree.
Use: the actual output gradient in local projected-residual estimates comes from the real policy execution.
Article: main_krylov, lem:projected-residual and lem:U(d), actual retained query coordinates.
Proof: retain the actual chronological pair transcript, preserve the actual
computed direction and actual current probe, and apply full physical invariance
of the real finite model-query tree under its genuine dimension cast. -/
theorem rfcCorrection_coordinates (memory : ℕ → ℕ) (count : ℕ) (H : History E)
    (s y : ℕ → E) (k : ℕ) (d z : E) (hshape : H.pairs=executedPairs s y k)
    (hd : d=windowDirection (selectedWindow memory H) H.gradient)
    (hgate : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) :
    let S := fun i : Fin (min (memory k) k) => s (k-1-i.val)
    let Y := fun i : Fin (min (memory k) k) => y (k-1-i.val)
    let U : Fin (min (memory k) k+1) → E := Fin.cons d S
    let Z : Fin (min (memory k) k+1) → E := Fin.cons z Y
    rfcCorrection memory count H z=repeatedModelTree U (pairModel U Z) count
      (searchedGradient H.gradient d z) := by
  -- The actual gate is already accepted; no decision is altered by the coefficient-coordinate identification.
  simp only [rfcCorrection]
  rw [ite_eq_left hgate,← hd,selectedWindow_of_executed_pairs memory H s y k hshape]
  have hc := augmentedWindow_coordinates s y k (memory k) d z
  exact repeatedModelTree_window_coordinates _ _ _ _ hc.1 hc.2 count _

/-- Every real total RFC step belongs to its actual current-plus-retained-age augmented coordinate span.
Use: transfer repeated projected-residual orders to the new genuinely recorded step without an assumed span witness.
Article: main_krylov, lem:projected-residual, actual recorded-step span.
Proof: every actual correction query stays in the genuine augmented observed
span, so its actual returned movement stays there. Add the actual line step
and identify this true list span with the proved fixed finite coordinate span. -/
theorem rfcStep_mem_augmented_coordinates (memory : ℕ → ℕ) (count : ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let method := rfcMethod memory count (E := E)
    let H := methodRun method A B g k
    let d := method.direction H
    let U : Fin (min (memory k) k+1) → E := Fin.cons d
      (fun i : Fin (min (memory k) k) => probedStep method A B g (k-1-i.val))
    probedStep method A B g k∈Submodule.span ℝ (Set.range U) := by
  -- Membership follows the real finite query execution, including a genuinely skipped gate.
  let method := rfcMethod memory count (E := E)
  let H := methodRun method A B g k
  let d := method.direction H
  let z := A k d
  let K := Submodule.span ℝ (Set.range (windowSteps ((d,z)::selectedWindow memory H)))
  have hd : d∈K := Submodule.subset_span ⟨0,rfl⟩
  have hmov : (probedPhase method A B g k).movement∈K :=
    runCorrections_movement_mem K _ (B k) _ ((rfcMethod_spanRestricted memory count H).2 z)
  have htot : probedStep method A B g k∈K := K.add_mem (K.smul_mem _ hd) hmov
  dsimp only [K] at htot
  rw [selectedWindow_methodRun] at htot
  have hc := (augmentedWindow_coordinates (probedStep method A B g) (probedSecant method A B g)
    k (memory k) d z).1
  rw [hc,(finCongr _).surjective.range_comp] at htot
  exact htot

end
end krylov.Methods
