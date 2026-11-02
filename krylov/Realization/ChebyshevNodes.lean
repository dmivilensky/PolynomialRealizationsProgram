import krylov.Realization.TerminalWeights
import chebyshev2.Continuum.ReferenceDeterminant

/-!
Article: main_krylov, prop:dict(i), the actual terminal Chebyshev nodes.
Use: remove any supplied-root premise from the genuine free-weight exact
recurrence construction by reusing the earlier actual cosine nodes.
Source: the proved finite Chebyshev node determinant product and strict
monotonicity of cosine on its actual interior angles.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 Real
open scoped BigOperators

/-- The actual descending cosine roots of the terminal Chebyshev polynomial, including the empty node set.
Use: The actual descending cosine roots of the terminal Chebyshev polynomial, including the empty node set.
Article: main_krylov, prop:dict(i).
Proof: Their genuine angles lie strictly between zero and pi; cosine is strictly decreasing there. -/
def chebyshevNodes (N : ℕ) : jacobi.Finite.Nodes N where
  value := SineJacobi.node N
  strictAnti := by
    intro i j hij
    have hi := SineJacobi.nodeAngle_mem N i
    have hj := SineJacobi.nodeAngle_mem N j
    apply cos_lt_cos_of_nonneg_of_le_pi hi.1.le hj.2.le
    have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by have := i.isLt;omega)
    unfold SineJacobi.nodeAngle
    apply (div_lt_div_iff_of_pos_right (by positivity : 0<(2 : ℝ)*N)).mpr
    have he : (i : ℝ)<(j : ℝ) := by exact_mod_cast hij
    nlinarith [pi_pos]
  interval i := by
    have hi := SineJacobi.nodeAngle_mem N i
    constructor
    · have h := cos_lt_cos_of_nonneg_of_le_pi hi.1.le (le_refl Real.pi) hi.2
      simpa only [SineJacobi.node,cos_pi] using h
    · have h := cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hi.2.le hi.1
      simpa only [SineJacobi.node,cos_zero] using h

/-- The actual monic polynomial of the constructed cosine nodes is exactly the terminal monic Chebyshev polynomial.
Use: The actual monic polynomial of the constructed cosine nodes is exactly the terminal monic Chebyshev polynomial.
Article: main_krylov, prop:dict(i).
Proof: Evaluate the genuine finite node determinant product and reuse its existing Chebyshev factorization. -/
theorem chebyshevNodes_polynomial (N : ℕ) (hN : 0<N) :
    (chebyshevNodes N).polynomial=fiberPolynomial N := by
  -- Reuse the exact finite determinant product, preserving its actual cosine nodes.
  apply Polynomial.funext
  intro x
  rw [fiberPolynomial_eq N hN]
  simpa only [jacobi.Finite.Nodes.polynomial,eval_prod,eval_sub,eval_X,eval_C,eval_mul,chebyshevNodes] using
    Continuum.chebyshev_node_product hN x

/-- Every positive spectral probability vector gives a genuine terminal-exact recurrence at the actual Chebyshev nodes.
Use: Every positive spectral probability vector gives a genuine terminal-exact recurrence at the actual Chebyshev nodes.
Article: main_krylov, prop:dict(i).
Proof: Instantiate the proved actual simplex reconstruction with the constructed genuine cosine node polynomial. -/
def freeWeightChebyshevRecurrence (I : SpectralInterval) (N : ℕ)
    (w : jacobi.Finite.WeightSimplex (N+1)) : ExactRecurrence I (N+1) :=
  weightedChebyshevRecurrence I (chebyshevNodes (N+1)) (chebyshevNodes_polynomial (N+1) (by omega)) w
end
end krylov.Realization
