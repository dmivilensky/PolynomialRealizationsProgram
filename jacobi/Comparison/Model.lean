import jacobi.Jacobi.Nodes
import jacobi.Finite.Persymmetric
import jacobi.Finite.Eigenvectors
import jacobi.Support.AffinePolynomials

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The actual target is the unique persymmetric reconstruction at the
original Jacobi zeros. Its actual spectral measure and orthogonal
polynomials are compared with the already constructed original
corrected support family; no second reconstruction is introduced.
Use: targetChain, targetPolynomial and targetGram all use this same genuine target measure and its actual reciprocal-derivative probabilities.
-/
namespace jacobi.Comparison
noncomputable section
open jacobi.Finite Polynomial

/-- The original positive target probability measure at the original Jacobi zeros.
Use: targetChain, targetPolynomial and targetGram all use this same genuine target measure and its actual reciprocal-derivative probabilities.
Article: jacobi, Theorem 2.1.
-/
def targetMeasure (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : DiscreteMeasure (n+1) :=
  (jacobi.Jacobi.nodes a b ha hb (n+1)).measure (jacobi.Jacobi.nodes a b ha hb (n+1)).persymmetricWeights

/-- The original unique persymmetric target Jacobi matrix.
Use: the eigenvectors and final candidate limit concern this actual matrix, reconstructed at the article's genuine ordered Jacobi roots.
Article: jacobi, Proposition C.3.
-/
def targetChain (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : chebyshev2.Jacobi (n+1) :=
  (persymmetricFiber (jacobi.Jacobi.nodes a b ha hb (n+1))).val

/-- The original target measure reconstructs exactly the original persymmetric target matrix.
Use: target Gram transformations and actual polynomial eigenvectors refer to precisely the same original finite candidate.
Article: jacobi, Proposition 2.2.
Proof: both definitions are the already proved canonical inverse-spectral reconstruction. -/
theorem targetMeasure_reconstructed (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (targetMeasure a b ha hb n).reconstructed=targetChain a b ha hb n := rfl

/-- The genuine target matrix belongs to the original complete Jacobi-polynomial fibre.
Use: all previously proved actual finite spectral limits and lower-bound transfer theorems apply to the same original candidate in Theorems A–B.
Article: jacobi, Theorem C.5.
Proof: the canonical persymmetric inverse reconstruction is defined inside that exact original fibre. -/
theorem targetChain_inFiber (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    InFiber (targetChain a b ha hb n) (jacobi.Jacobi.nodes a b ha hb (n+1)).polynomial :=
  (persymmetricFiber (jacobi.Jacobi.nodes a b ha hb (n+1))).property

/-- The actual original target matrix is genuinely persymmetric.
Use: its complete eigenvector parity extends half-chain convergence to the full physical interval in Appendix C.4 and Theorem 2.1.
Article: jacobi, Proposition C.3.
Proof: reuse the full proved canonical persymmetric reconstruction theorem for the actual original Jacobi node family. -/
theorem targetChain_persymmetric (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (targetChain a b ha hb n).matrix.submatrix Fin.rev Fin.rev=(targetChain a b ha hb n).matrix :=
  persymmetricFiber_symmetric (jacobi.Jacobi.nodes a b ha hb (n+1))

/-- The actual canonical target orthogonal polynomial in its original spectral measure.
Use: the target Gram–Cholesky identities and actual target eigenvectors concern this same polynomial, with its true degree and positive leading coefficient.
Article: jacobi, Proposition C.3.
-/
def targetPolynomial (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) : ℝ[X] :=
  (targetMeasure a b ha hb n).orthogonalPolynomial i

/-- The genuine target eigenvectors are the original positive square-root probabilities times the actual target polynomials.
Use: Appendix C.4 and Theorem 2.1 pass the same actual Gram–Cholesky polynomial asymptotics to the actual finite physical eigenvectors.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: the already constructed spectral basis of the actual target measure has the proved complete polynomial entry formula. -/
theorem target_eigenvector_polynomial (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i k:Fin (n+1)) :
    (targetMeasure a b ha hb n).reconstructedBasis.Q i k=
      Real.sqrt ((targetMeasure a b ha hb n).weight k)*
        (targetPolynomial a b ha hb n i).eval ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k) :=
  (targetMeasure a b ha hb n).eigenvectors_polynomial i k

end
end jacobi.Comparison
