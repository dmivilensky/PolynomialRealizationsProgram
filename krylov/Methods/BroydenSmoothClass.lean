import krylov.Methods.CorrectionFree
import krylov.Methods.EmptyCompilation
import krylov.Methods.BroydenObserved
import krylov.Methods.BroydenReference

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, actual smooth convex Broyden class membership.
Use: package genuine positive-scalar-initialized inverse convex Broyden methods with arbitrary prescribed closed-unit-interval interpolation schedules as actual smooth globally CG-consistent source methods.
Source: Nazareth79 and Dixon72a/Dixon72b; genuine full observed-pair execution, actual positive reference secant/inverse-curvature pivots and proved native finite observation coefficient regularity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full inverse convex Broyden executor has genuine primitive C-r local coefficient charts on every true active quadratic reference cycle.
Use: The actual full inverse convex Broyden executor has genuine primitive C-r local coefficient charts on every true active quadratic reference cycle.
Article: main_krylov, def:classes and cor:lm, actual smooth convex Broyden class membership.
Proof: Compile the real finite observed coefficient program and derive every genuine chronological secant and inverse-curvature pivot from actual CG reference execution. -/
theorem broydenMethod_smoothCycleAt (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (broydenMethod c θ) r Q g N := by
  -- Actual coefficient compilation derives the genuine finite smooth cycle without assuming output or trajectory regularity.
  apply emptyCompiled_smoothCycleAt (broydenMethod c θ) (fun _ _ => rfl)
    (broydenObservedRule c θ) (broydenObservedRule_evaluate c θ) Q g N r
  intro k hk
  apply broydenObservedRule_regular
  -- Real quadratic execution identifies the actual full pair history and proves both genuine inverse pivot domains.
  have hW : chartWindow fullMemory (methodRun (broydenMethod c θ) (fun _ => Q) (fun _ => Q) g k).queryShape
      (observedArray (methodRun (broydenMethod c θ) (fun _ => Q) (fun _ => Q) g k).observationList.length
        (methodRun (broydenMethod c θ) (fun _ => Q) (fun _ => Q) g k).observationList)=
      referencePairs Q g k := by
    unfold chartWindow
    rw [ofFn_observedArray,historyFromObservations_actual,selectedWindow_full]
    exact (broydenMethod_static c hc θ hθ Q hQ hpos g k).2
  rw [hW]
  exact broyden_reference_pivots c hc θ hθ Q hQ hpos g k (fun i hi => hpre i (hi.trans hk))

/-- The actual positive-scalar-initialized inverse convex Broyden executor is a genuine primitive smooth globally CG-consistent source-class member for every prescribed convex parameter schedule.
Use: The actual positive-scalar-initialized inverse convex Broyden executor is a genuine primitive smooth globally CG-consistent source-class member for every prescribed convex parameter schedule.
Article: main_krylov, def:classes and cor:lm, actual smooth convex Broyden class membership.
Proof: Combine true all-history source information admissibility, actual global quadratic CG consistency and derived real primitive coefficient membership. -/
def smoothBroydenClass (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1) : SmoothProbedClass E where
  memory := fullMemory
  policy := broydenMethod c θ
  admissible := broydenMethod_spanRestricted c θ
  consistent := broydenMethod_consistent c hc θ hθ
  smooth := fun Q hQ hpos g N hpre => broydenMethod_smoothCycleAt c hc θ hθ Q hQ hpos g N hpre 2

/-- Every genuine smooth convex Broyden class member has actual empty correction phases on all histories.
Use: Every genuine smooth convex Broyden class member has actual empty correction phases on all histories.
Article: main_krylov, def:classes and cor:lm, actual smooth convex Broyden class membership.
Proof: Its real raw implementation makes no correction query. -/
theorem smoothBroydenClass_correctionFree (c : ℝ) (hc : 0<c) (θ : ℕ → ℝ) (hθ : ∀ i,0≤θ i ∧ θ i≤1) :
    CorrectionFree (smoothBroydenClass (E := E) c hc θ hθ).policy := fun _ _ => rfl
end
end krylov.Methods
