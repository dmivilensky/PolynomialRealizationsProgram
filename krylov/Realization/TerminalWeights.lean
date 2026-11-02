import jacobi.Finite.WeightChart
import chebyshev2.Finite.Equivalence
import krylov.Realization.RawCGCoefficients

/-!
Article: main_krylov, prop:dict(i), terminal Chebyshev spectrum and free weights.
Use: reuse the complete jacobi inverse spectral simplex chart and the proved
finite Jacobi/recurrence equivalence to construct genuinely exact realizations
with every prescribed positive first-site spectral probability vector.
Source: de Boor--Golub reconstruction in jacobi and the terminal Chebyshev
coefficient equivalence in chebyshev2.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Terminal Chebyshev exactness of a genuine Jacobi matrix is equivalent to its actual characteristic polynomial being the monic Chebyshev polynomial.
Use: Terminal Chebyshev exactness of a genuine Jacobi matrix is equivalent to its actual characteristic polynomial being the monic Chebyshev polynomial.
Article: main_krylov, prop:dict(i).
Proof: Reuse the actual characteristic-continuant identity in both directions. -/
theorem fibre_terminal_iff (J : chebyshev2.Jacobi N) :
    J.Terminal ↔ J.matrix.charpoly=fiberPolynomial N := by
  constructor
  · exact J.charpoly_eq
  · intro h
    rw [Jacobi.matrix,← J.data.block_eq_charpoly J.coupling_nonneg] at h
    exact h

/-- Every positive spectral probability vector constructs a genuine terminal-exact Chebyshev recurrence at the prescribed Chebyshev nodes.
Use: Every positive spectral probability vector constructs a genuine terminal-exact Chebyshev recurrence at the prescribed Chebyshev nodes.
Article: main_krylov, prop:dict(i).
Proof: The complete jacobi simplex reconstruction supplies the actual Jacobi matrix; its true characteristic polynomial gives terminality and the existing physical recurrence is terminal-exact. -/
def weightedChebyshevRecurrence (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (hS : S.polynomial=fiberPolynomial (N+1)) (w : jacobi.Finite.WeightSimplex (N+1)) :
    ExactRecurrence I (N+1) := by
  let J := jacobi.Finite.reconstructFiber S w
  have ht : J.val.Terminal := (fibre_terminal_iff J.val).mpr (J.property.2.trans hS)
  exact ⟨J.val.recurrence I (J.val.admissible I (by omega) ht), J.val.recurrence_terminal I (by omega) ht⟩

/-- The genuine reconstructed terminal-exact recurrence has exactly the prescribed free positive spectral weights.
Use: The genuine reconstructed terminal-exact recurrence has exactly the prescribed free positive spectral weights.
Article: main_krylov, prop:dict(i).
Proof: The actual Jacobi/recurrence inverse returns the original simplex reconstruction, whose genuine first-site weights are the input probabilities. -/
theorem weightedChebyshevRecurrence_weights (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (hS : S.polynomial=fiberPolynomial (N+1)) (w : jacobi.Finite.WeightSimplex (N+1)) :
    let R := weightedChebyshevRecurrence I S hS w
    let J := R.val.jacobi I
    ∃ hJ : jacobi.Finite.InFiber J S.polynomial,
      jacobi.Finite.spectralWeights S ⟨J,hJ⟩=w := by
  -- Identify the actual inverse Jacobi matrix before reading its true spectral weights.
  let J := jacobi.Finite.reconstructFiber S w
  have ht : J.val.Terminal := (fibre_terminal_iff J.val).mpr (J.property.2.trans hS)
  have he : (weightedChebyshevRecurrence I S hS w).val.jacobi I=J.val := by
    exact J.val.jacobi_recurrence I (J.val.admissible I (by omega) ht)
  dsimp only
  refine ⟨he ▸ J.property, ?_⟩
  convert jacobi.Finite.spectralWeights_reconstruct S w using 1
  congr 1
  exact Subtype.ext he
end
end krylov.Realization
