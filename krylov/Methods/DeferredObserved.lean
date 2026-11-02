import krylov.Methods.DeferredCoefficients
import krylov.Methods.FCObservedRule

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual observed deferred direction compiler.
Use: represent the genuine deferred solve by true finite observed-vector
coefficients and derive their actual primitive regularity.
Source: actual coefficient-history synthesis and existing genuine smooth
conjugacy/model observed solves.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The actual finite observed-vector coefficient rule for the genuine deferred-cancellation direction.
Use: The actual finite observed-vector coefficient rule for the genuine deferred-cancellation direction.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual observed deferred direction compiler.
Proof: Read true current-gradient and retained-step coefficients and compute the actual tilted observed solve. -/
def deferredObservedRule (memory : ℕ → ℕ) (shape : List ℕ) (n : ℕ) (a : ℝ) : ObservedRule E n where
  coefficient data := -(coefficientHistory shape n).gradient+
    ∑ i : Fin (min (memory shape.length) shape.length),
      deferredCoefficients (chartSteps memory shape data) (chartImages memory shape data) (chartGradient shape data) a i •
        coefficientStep memory shape n i

/-- The genuine deferred observed rule synthesizes exactly the actual finite physical tilted direction.
Use: The genuine deferred observed rule synthesizes exactly the actual finite physical tilted direction.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual observed deferred direction compiler.
Proof: The true observation synthesis map preserves the genuine current gradient and each real retained-step column and finite coefficient combination. -/
theorem deferredObservedRule_evaluate (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) (a : ℝ) :
    (deferredObservedRule memory shape n a).evaluate data=
      deferredDirection (chartSteps memory shape data) (chartImages memory shape data) (chartGradient shape data) a := by
  change observationSynthesis data (-(coefficientHistory shape n).gradient+
    ∑ i : Fin (min (memory shape.length) shape.length),
      deferredCoefficients (chartSteps memory shape data) (chartImages memory shape data) (chartGradient shape data) a i •
        coefficientStep memory shape n i)=_
  -- Synthesize the real current gradient and each genuine retained column through the actual observation map.
  rw [map_add,map_neg,map_sum,← chartGradient_synthesis]
  have he (i : Fin (min (memory shape.length) shape.length)) :
      observationSynthesis data (coefficientStep memory shape n i)=chartSteps memory shape data i :=
    (chartSteps_synthesis memory shape data i).1.symm
  simp_rw [map_smul,he]
  rfl

/-- The true finite deferred observed coefficients are C-r on the genuine nonsingular actual cross-Gram domain.
Use: The true finite deferred observed coefficients are C-r on the genuine nonsingular actual cross-Gram domain.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual observed deferred direction compiler.
Proof: Compose the actual reconstructed observed columns and gradient with the proved genuine deferred coefficient calculus. -/
theorem deferredObservedRule_coefficient_regular (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) (a : ℝ)
    (hC : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0)
    (r : WithTop ℕ∞) : ContDiffAt ℝ r (deferredObservedRule memory shape n a : ObservedRule E n).coefficient data := by
  -- Every true coefficient-domain premise is derived from the genuine reconstructed observed chart.
  have hfields := chartSteps_regular memory shape (fun p : Fin n → E => p) data (r := r) contDiffAt_id
  have hgrad := (chartWindow_regular memory shape (fun p : Fin n → E => p) data (r := r) contDiffAt_id).2
  have hc := contDiff_deferredCoefficients (fun p : Fin n → E => chartSteps memory shape p)
    (fun p => chartImages memory shape p) (fun p => chartGradient shape p) a data
    (fun i => (hfields i).1) (fun i => (hfields i).2) hgrad hC
  change ContDiffAt ℝ r (fun p : Fin n → E => -(coefficientHistory shape n).gradient+
    ∑ i : Fin (min (memory shape.length) shape.length),
      deferredCoefficients (chartSteps memory shape p) (chartImages memory shape p) (chartGradient shape p) a i •
        coefficientStep memory shape n i) data
  exact contDiffAt_const.add (ContDiffAt.sum (fun i _ => (hc i).smul contDiffAt_const))
end
end krylov.Methods
