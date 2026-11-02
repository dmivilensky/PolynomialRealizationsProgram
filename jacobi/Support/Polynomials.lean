import jacobi.Support.Measures
import jacobi.Finite.NormalizedPolynomials

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
Use: top-node products, the genuine spectral Volterra equation and uniform support envelopes all concern this same actual spectral orthogonal polynomial.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial jacobi.Finite chebyshev1 chebyshev2

/-- The actual original natural support polynomial, with its original leading-continuant and positive coupling-product normalization.
Use: top-node products, the genuine spectral Volterra equation and uniform support envelopes all concern this same actual spectral orthogonal polynomial.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def naturalPolynomial (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m : ℕ) : ℝ[X] :=
  normalizedLeading (naturalChain a b ha hb (n+1)) m

/-- The original natural recurrence polynomial is exactly the actual canonical orthogonal polynomial of its genuine original spectral measure.
Use: the support asymptotics are connected to the actual spectral measure used by the finite Gram matrix and Cholesky transformation.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: the actual original spectral measure reconstructs exactly the original sine-coefficient matrix, and the proved general normalized-continuant identification gives the same actual polynomial. -/
theorem naturalPolynomial_eq (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i:Fin (n+1)) :
    naturalPolynomial a b ha hb n i=(naturalMeasure a b ha hb n).orthogonalPolynomial i := by
  have h := normalizedLeading_eq_orthogonalPolynomial (naturalMeasure a b ha hb n) i
  rw [naturalMeasure_reconstructed] at h
  exact h

/-- The actual original natural support polynomial has its precise degree and genuinely positive leading coefficient.
Use: the original Volterra wave and finite Gram coordinate transformations preserve the source's canonical polynomial normalization.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: identify the original recurrence polynomial with the independently constructed genuine spectral orthogonal polynomial and reuse its proved exact degree and positive leading coefficient. -/
theorem naturalPolynomial_degree (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i:Fin (n+1)) :
    (naturalPolynomial a b ha hb n i).natDegree=i.val ∧
      0<(naturalPolynomial a b ha hb n i).leadingCoeff := by
  rw [naturalPolynomial_eq]
  exact (naturalMeasure a b ha hb n).orthogonalPolynomial_degree i

/-- The actual original natural support wave at arbitrary complex energy.
Use: the original Volterra equation and frequency envelopes apply to this same genuine polynomial extension, without a separately postulated analytic wave.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def naturalWave (a b : ℝ) (ha : -1<a) (hb : -1<b) (n m : ℕ) (z : ℂ) : ℂ :=
  Polynomial.aeval z (naturalPolynomial a b ha hb n m)

/-- The actual corrected original support orthogonal polynomials in their genuine original spectral measure.
Use: these are the original psi_(n,m)^0 inputs to the target-measure finite Gram matrix, with full actual reconstruction established in supportMeasure_reconstructed.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def supportPolynomial (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i:Fin (n+1)) : ℝ[X] :=
  (supportMeasure a b ha hb n).orthogonalPolynomial i

/-- The actual corrected original support polynomial is exactly the original normalized leading-continuant polynomial of the actual corrected chain.
Use: affine polynomial comparison and the genuine target/support Gram matrices keep the original physical recurrence and canonical spectral family identical.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: the actual original corrected spectral measure reconstructs the same original corrected support matrix; apply the general genuine normalized-continuant identification. -/
theorem supportPolynomial_eq_normalized (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (i:Fin (n+1)) :
    supportPolynomial a b ha hb n i=normalizedLeading (supportChain a b ha hb (n+1)) i := by
  have h := normalizedLeading_eq_orthogonalPolynomial (supportMeasure a b ha hb n) i
  rw [supportMeasure_reconstructed] at h
  exact h.symm

end
end jacobi.Support
