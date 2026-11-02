import krylov.Methods.HistoryWindowCharts
import krylov.Stability.ContDiffSolve

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, actual primitive FC coefficient rules.
Use: represent the real retained-window FC direction as a genuine finite
observed linear combination with true C-r primitive coefficients on its
actual cross-Gram inverse domain, for every fixed query-history shape.
Source: genuine fixed coefficient-history synthesis, actual retained-pair
coordinate solves and proved true primitive conjugacy-coefficient regularity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The genuine fixed observation coefficients of each true retained step for the prescribed actual query-history shape.
Use: The genuine fixed observation coefficients of each true retained step for the prescribed actual query-history shape.
Article: main_krylov, def:classes and cor:lm, actual primitive FC coefficient rules.
Proof: Read the real retained-step coordinate from the true standard coefficient history. -/
def coefficientStep (memory : ℕ → ℕ) (shape : List ℕ) (n : ℕ)
    (i : Fin (min (memory shape.length) shape.length)) : Fin n → ℝ :=
  (((selectedWindow memory (coefficientHistory shape n)).getD i.val (0,0)).1)

/-- The actual primitive observed-vector coefficient rule for the genuine retained-window FC direction on a fixed true query-history shape.
Use: The actual primitive observed-vector coefficient rule for the genuine retained-window FC direction on a fixed true query-history shape.
Article: main_krylov, def:classes and cor:lm, actual primitive FC coefficient rules.
Proof: Use the true coefficient-history gradient and real retained-step coefficient vectors with the actual computed conjugacy coefficients. -/
def fcObservedRule (memory : ℕ → ℕ) (shape : List ℕ) (n : ℕ) : ObservedRule E n where
  coefficient data := -(coefficientHistory shape n).gradient+
    ∑ i : Fin (min (memory shape.length) shape.length),
      conjugacyCoefficients (chartSteps memory shape data) (chartImages memory shape data) (chartGradient shape data) i •
        coefficientStep memory shape n i

/-- The genuine primitive FC observed rule evaluates exactly to the actual retained-window direction of its true reconstructed input history.
Use: The genuine primitive FC observed rule evaluates exactly to the actual retained-window direction of its true reconstructed input history.
Article: main_krylov, def:classes and cor:lm, actual primitive FC coefficient rules.
Proof: Synthesize the real coefficient-history gradient and retained steps through the genuine linear observation map. Its actual finite sum is precisely the implemented true retained-window conjugacy solve. -/
theorem fcObservedRule_evaluate (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) :
    (fcObservedRule memory shape n).evaluate data=
      windowDirection (chartWindow memory shape data) (chartGradient shape data) := by
  -- Synthesize true fixed history coefficients through the genuine original observations, without assuming their linear independence.
  change observationSynthesis data (-(coefficientHistory shape n).gradient+
    ∑ i : Fin (min (memory shape.length) shape.length),
      conjugacyCoefficients (chartSteps memory shape data) (chartImages memory shape data) (chartGradient shape data) i •
        coefficientStep memory shape n i)=_
  rw [map_add,map_neg,map_sum,← chartGradient_synthesis]
  have he (i : Fin (min (memory shape.length) shape.length)) :
      observationSynthesis data (coefficientStep memory shape n i)=chartSteps memory shape data i :=
    (chartSteps_synthesis memory shape data i).1.symm
  simp_rw [map_smul,he]
  rw [chartWindow_direction]
  rfl

/-- Every genuine primitive FC observed coefficient is C-r at its actual true nonsingular retained cross-Gram domain.
Use: Every genuine primitive FC observed coefficient is C-r at its actual true nonsingular retained cross-Gram domain.
Article: main_krylov, def:classes and cor:lm, actual primitive FC coefficient rules.
Proof: True reconstructed observations supply genuine C-r retained steps, actual secants and the real current gradient. Apply the proved primitive conjugacy-coefficient calculus and multiply only by genuine fixed observation coefficient vectors. -/
theorem fcObservedRule_coefficient_regular (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (hC : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0)
    (r : WithTop ℕ∞) : ContDiffAt ℝ r (fcObservedRule memory shape n : ObservedRule E n).coefficient data := by
  -- Derive the real primitive coefficient regularity directly on the finite observed-data space, not on an assumed cycle map.
  have hfields := chartSteps_regular memory shape (fun p : Fin n → E => p) data (r := r) contDiffAt_id
  have hgrad := (chartWindow_regular memory shape (fun p : Fin n → E => p) data (r := r) contDiffAt_id).2
  have hc := contDiff_conjugacyCoefficients (fun p : Fin n → E => chartSteps memory shape p)
    (fun p => chartImages memory shape p) (fun p => chartGradient shape p) data
    (fun i => (hfields i).1) (fun i => (hfields i).2) hgrad hC
  change ContDiffAt ℝ r (fun p : Fin n → E => -(coefficientHistory shape n).gradient+
    ∑ i : Fin (min (memory shape.length) shape.length),
      conjugacyCoefficients (chartSteps memory shape p) (chartImages memory shape p) (chartGradient shape p) i •
        coefficientStep memory shape n i) data
  exact contDiffAt_const.add (ContDiffAt.sum (fun i _ => (hc i).smul contDiffAt_const))
end
end krylov.Methods
