import jacobi.Comparison.Model
import jacobi.Finite.GramCholesky

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Its exact perturbation formula, positive definiteness and genuine
positive Cholesky transformation have no asymptotic premises.
Use: its principal half-chain section is the original I+B_n whose two-edge kernel and uniform coercivity are required by the final eigenvector limit.
-/
namespace jacobi.Comparison
noncomputable section
open jacobi.Finite jacobi.Support Polynomial Matrix
open scoped InnerProductSpace

/-- The full original target Gram matrix of the genuine corrected support polynomials.
Use: its principal half-chain section is the original I+B_n whose two-edge kernel and uniform coercivity are required by the final eigenvector limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def targetGram (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => ∑k:Fin (n+1),(targetMeasure a b ha hb n).weight k*
    (supportPolynomial a b ha hb n i).eval ((targetMeasure a b ha hb n).node k)*
    (supportPolynomial a b ha hb n j).eval ((targetMeasure a b ha hb n).node k)

/-- The actual target Gram perturbation from the identity in the original corrected support basis.
Use: targetGram_perturbation_terms is the exact spectral summand representation used in the original two-edge Gram limit.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def gramPerturbation (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  targetGram a b ha hb n-1

/-- The actual target Gram matrix is precisely the Hilbert Gram matrix of genuine weighted original support polynomial evaluations.
Use: targetGram_posDef and targetGram_factor apply the proved finite Gram–Cholesky machinery to the actual article data.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the proved original weighted evaluation inner product is exactly the displayed finite spectral sum. -/
theorem targetGram_eq (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    targetGram a b ha hb n=Matrix.gram ℝ
      (fun i => (targetMeasure a b ha hb n).evaluate (supportPolynomial a b ha hb n i)) := by
  ext i j
  exact ((targetMeasure a b ha hb n).inner_evaluate _ _).symm

/-- The genuine corrected support polynomials have exactly the identity Gram matrix in their original support measure.
Use: targetGram_perturbation_terms subtracts the true support identity from the actual target Gram matrix, yielding the original Appendix E spectral representation.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the actual canonical support polynomial basis is orthonormal in the same original support spectral measure. -/
theorem support_gram_identity (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) :
    (∑k:Fin (n+1),(supportMeasure a b ha hb n).weight k*
      (supportPolynomial a b ha hb n i).eval ((supportMeasure a b ha hb n).node k)*
      (supportPolynomial a b ha hb n j).eval ((supportMeasure a b ha hb n).node k))=
      if i=j then 1 else 0 := by
  rw [← (supportMeasure a b ha hb n).inner_evaluate]
  simp only [supportPolynomial,DiscreteMeasure.evaluate_orthogonalPolynomial]
  exact (supportMeasure a b ha hb n).polynomialBasis.inner_eq_ite i j

/-- The actual original Gram perturbation is exactly the sum of the original target-minus-support spectral terms.
Use: the genuine two-edge Gram convergence estimates the same Appendix E summands, retaining the actual target and support probabilities and nodes.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: subtract the proved exact support orthonormality identity from the definition of the genuine original target Gram entry and distribute the finite sum. -/
theorem targetGram_perturbation_terms (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) :
    gramPerturbation a b ha hb n i j=
      ∑k:Fin (n+1),((targetMeasure a b ha hb n).weight k*
        (supportPolynomial a b ha hb n i).eval ((targetMeasure a b ha hb n).node k)*
        (supportPolynomial a b ha hb n j).eval ((targetMeasure a b ha hb n).node k)-
      (supportMeasure a b ha hb n).weight k*
        (supportPolynomial a b ha hb n i).eval ((supportMeasure a b ha hb n).node k)*
        (supportPolynomial a b ha hb n j).eval ((supportMeasure a b ha hb n).node k)) := by
  rw [Finset.sum_sub_distrib,support_gram_identity]
  rfl

/-- The actual full target Gram matrix is strictly positive definite at every original finite dimension.
Use: the genuine original Cholesky and Schur formulas have all invertibility premises discharged; the later uniform coercivity estimate strengthens this qualitative positivity quantitatively.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the true corrected support polynomials have their actual successive degrees and positive leading coefficients. Distinct original target nodes and positive actual target weights give strict positivity by the proved Vandermonde Gram theorem. -/
theorem targetGram_posDef (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (targetGram a b ha hb n).PosDef :=
  (targetMeasure a b ha hb n).gram_posDef (supportPolynomial a b ha hb n)
    (fun i => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree i).1)
    (fun i => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree i).2.ne')

/-- The actual original positive lower triangular Cholesky factor of the genuine target Gram matrix.
Use: targetPolynomial_cholesky and its Schur row form transform the actual original support family into the actual target polynomials used in the eigenvectors.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def targetLower (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (targetMeasure a b ha hb n).gramLower (supportPolynomial a b ha hb n)

/-- The genuine original target Gram matrix factors as its actual positive Cholesky factor times its transpose.
Use: targetPolynomial_cholesky uses this same actual factor in the original finite polynomial transformation, prior to estimating its continuum limit.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: apply the proved finite Gram–Schmidt factorization to the actual target-weighted support polynomial evaluations. -/
theorem targetGram_factor (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    targetGram a b ha hb n=targetLower a b ha hb n*(targetLower a b ha hb n)ᵀ := by
  rw [targetGram_eq]
  exact Gram.factorization (by simp) _

/-- The actual original target polynomials are exactly the inverse actual Cholesky transformation of the genuine corrected support polynomials.
Use: Appendix C.4 inserts this exact original transformation before taking the target's continuum limit.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the genuine support basis has its proved original degrees and positive leading coefficients. The proved change-of-measure uniqueness theorem identifies the actual inverse Gram transformation with the canonical target polynomials. -/
theorem targetPolynomial_cholesky (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) :
    targetPolynomial a b ha hb n i=
      ∑j:Fin (n+1),(targetLower a b ha hb n)⁻¹ i j • supportPolynomial a b ha hb n j := by
  exact ((targetMeasure a b ha hb n).changeOfMeasure_eq (supportPolynomial a b ha hb n)
    (fun j => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree j).1)
    (fun j => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree j).2) i).symm

end
end jacobi.Comparison
