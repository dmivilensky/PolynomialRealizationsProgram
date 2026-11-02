import krylov.Reference.GaussCGCoefficients
import krylov.Envelope.ContinuationCongruence
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), genuine finite Gauss continuation coherence.
Use: identify every actual used continuation of the original Gaussian rules with the common measured coefficient sequence before termination.
Source: actual Gaussian CG coefficient dictionary and the proved exact used-coefficient dependence of the true continuation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference Matrix Polynomial chebyshev1

/-- Every actual finite Gaussian CG continuation equals the genuine common original coefficient continuation on its used chronological suffix.
Use: Every actual finite Gaussian CG continuation equals the genuine common original coefficient continuation on its used chronological suffix.
Article: main_krylov, prop:phi(c), genuine finite Gauss continuation coherence.
Proof: Replace only true used line and internal recurrence coefficients; the actual unused terminating beta does not enter. -/
theorem gauss_phi_common (J : JacobiData) (hpos : ∀ n,0<n → 0<J.aSq n)
    (mu : ℝ) (hmu : 0<mu)
    (hlo : ∀ N,(jacobiPrefix J.b (fun n => Real.sqrt (J.aSq (n+1))) N-mu • 1).PosSemidef)
    (N j r : ℕ) (hjr : j+r≤N) :
    let g : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)
    let d := jacobiPivot J.b (fun n => Real.sqrt (J.aSq (n+1)))
    phi (CG.length (cgOperator (J.matrix 0 N)) g) (CG.beta (cgOperator (J.matrix 0 N)) g) j r=
      phi (fun n => (d n)⁻¹) (fun n => (Real.sqrt (J.aSq (n+1))/d n)^2) j r := by
  dsimp only
  apply phi_coefficients_congr
  · intro i hi
    exact (gauss_cg_coefficients J hpos mu hmu hlo N (j+i) (by omega)).1
  · intro i hi
    exact (gauss_cg_coefficients J hpos mu hmu hlo N (j+i) (by omega)).2.1 (by omega)
end
end krylov.Envelope
