import krylov.Methods.FC
import krylov.Methods.ReferenceModels

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred-cancellation direction.
Use: construct the genuine data-only tilted conjugacy solve and prove
its real observed-span and exact residual-cancellation equations.
Source: actual observed cross-Gram solves and the genuine finite matrix
inverse identity on the true nonsingular model domain.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual deferred-cancellation direction coefficients use the genuine observed conjugacy and old residual right-hand sides.
Use: The actual deferred-cancellation direction coefficients use the genuine observed conjugacy and old residual right-hand sides.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred-cancellation direction.
Proof: Solve the true observed cross-Gram system with the actual prescribed inverse step estimate. -/
def deferredCoefficients (s y : ι → E) (g : E) (a : ℝ) : ι → ℝ :=
  (crossGram y s)⁻¹ *ᵥ (coordinates y g-a⁻¹ • coordinates s g)

/-- The genuine deferred-cancellation direction is the real current negative gradient plus its actual observed-step combination.
Use: The genuine deferred-cancellation direction is the real current negative gradient plus its actual observed-step combination.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred-cancellation direction.
Proof: Use the true finite data-only tilted coefficients. -/
def deferredDirection (s y : ι → E) (g : E) (a : ℝ) : E :=
  -g+combine s (deferredCoefficients s y g a)

/-- The actual deferred-cancellation direction lies in the genuine current-gradient and stored-step span.
Use: The actual deferred-cancellation direction lies in the genuine current-gradient and stored-step span.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred-cancellation direction.
Proof: Every real correction coefficient multiplies a true observed stored step. -/
theorem deferredDirection_mem_span (s y : ι → E) (g : E) (a : ℝ) :
    deferredDirection s y g a∈Submodule.span ℝ (insert g (Set.range s)) := by
  apply Submodule.add_mem
  · exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_insert _ _))
  · exact (Submodule.span_mono (Set.subset_insert _ _)) (combine_mem_span _ _)

/-- Zero true old-step residual coordinates make the actual deferred direction exactly the genuine untilted conjugacy direction.
Use: Zero true old-step residual coordinates make the actual deferred direction exactly the genuine untilted conjugacy direction.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred-cancellation direction.
Proof: The real tilted right-hand-side term vanishes, including totalized singular solved-tail models. -/
theorem deferredDirection_eq_conjugacy (s y : ι → E) (g : E) (a : ℝ)
    (hz : coordinates s g=0) : deferredDirection s y g a=conjugacyDirection s y g := by
  simp only [deferredDirection,deferredCoefficients,hz,smul_zero,sub_zero]
  rfl

/-- The actual nonsingular deferred direction has exactly the prescribed genuine inverse-estimate old secant/gradient pairings.
Use: The actual nonsingular deferred direction has exactly the prescribed genuine inverse-estimate old secant/gradient pairings.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred-cancellation direction.
Proof: Multiply the genuine inverse solve by its true observed cross-Gram matrix and cancel the actual current secant-gradient right-hand side. -/
theorem deferredDirection_conjugacy (s y : ι → E) (g : E) (a : ℝ)
    (hdet : IsUnit (crossGram y s).det) (i : ι) :
    inner ℝ (y i) (deferredDirection s y g a)= -a⁻¹*inner ℝ (s i) g := by
  -- Use the genuine nonsingular observed matrix to identify the real tilted old-secant pairing coordinates.
  have hc : coordinates y (deferredDirection s y g a)= -a⁻¹ • coordinates s g := by
    have he := coordinates_combine y s (deferredCoefficients s y g a)
    rw [deferredCoefficients,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hdet,Matrix.one_mulVec] at he
    ext j
    change inner ℝ (y j) (-g+combine s (deferredCoefficients s y g a))=(-a⁻¹)*inner ℝ (s j) g
    rw [inner_add_right,inner_neg_right,show inner ℝ (y j) (combine s (deferredCoefficients s y g a))=
      inner ℝ (y j) g-a⁻¹*inner ℝ (s j) g from congrFun he j]
    ring
  exact congrFun hc i
end
end krylov.Methods
