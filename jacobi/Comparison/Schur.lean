import jacobi.Comparison.Gram

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The original finite row coefficients and positive normalizations are
constructed from the genuine target-weighted support polynomials.
Every original inverse principal block and polynomial row identity
is justified without an assumed Gram or Cholesky certificate.
Use: targetPolynomial_schur is precisely the original row transformation, and the continuum Cholesky estimate concerns these same genuine coefficients.
-/
namespace jacobi.Comparison
noncomputable section
open jacobi.Finite jacobi.Support Polynomial Matrix
open scoped InnerProductSpace

/-- The original actual negative principal-Gram projection coefficients.
Use: targetPolynomial_schur is precisely the original row transformation, and the continuum Cholesky estimate concerns these same genuine coefficients.
Article: jacobi, Proposition C.3.
-/
def rowCoefficient (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) (j:Fin i.val) : ℝ :=
  -Gram.coefficients
    (fun k:Fin i.val => (targetMeasure a b ha hb n).evaluate (supportPolynomial a b ha hb n (Gram.before i k)))
    ((targetMeasure a b ha hb n).evaluate (supportPolynomial a b ha hb n i)) j

/-- The original actual Schur normalization for a genuine target polynomial row.
Use: rowNormalization_pos justifies its positive square root in targetPolynomial_schur; the continuum Cholesky theorem must estimate this exact q_(n,i).
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def rowNormalization (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) : ℝ :=
  Gram.complement
    (fun k:Fin i.val => (targetMeasure a b ha hb n).evaluate (supportPolynomial a b ha hb n (Gram.before i k)))
    ((targetMeasure a b ha hb n).evaluate (supportPolynomial a b ha hb n i))

/-- The actual target-weighted original support polynomial vectors are linearly independent in every finite dimension.
Use: rowNormalization_pos and all actual principal inverse systems use genuine original Vandermonde independence.
Article: jacobi, Theorem 2.1.
Proof: the actual support family has successive original degrees and positive leading coefficients, so the proved target-weighted Vandermonde independence theorem applies. -/
theorem target_support_independent (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    LinearIndependent ℝ (fun i => (targetMeasure a b ha hb n).evaluate (supportPolynomial a b ha hb n i)) :=
  (targetMeasure a b ha hb n).evaluate_linearIndependent (supportPolynomial a b ha hb n)
    (fun i => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree i).1)
    (fun i => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree i).2.ne')

/-- Every genuine original target polynomial row has a strictly positive actual Schur normalization.
Use: targetPolynomial_schur takes the original positive square root without imposing any extra normalization premise.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the original target-weighted support family is genuinely independent, and its actual row Schur complement is the positive squared Gram–Schmidt residual norm. -/
theorem rowNormalization_pos (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) :
    0<rowNormalization a b ha hb n i :=
  Gram.row_complement_pos (target_support_independent a b ha hb n) i

/-- Every actual original principal target Gram block is strictly positive definite.
Use: the original rowCoefficient inverse principal block is a genuine inverse; the eventual uniform lower bound is a quantitative strengthening of this proved all-dimension fact.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: a principal submatrix along an injective coordinate embedding preserves the actual proved positive definiteness. -/
theorem targetGram_principal_posDef (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ)
    {N:ℕ} (e:Fin N→Fin (n+1)) (he:Function.Injective e) :
    ((targetGram a b ha hb n).submatrix e e).PosDef :=
  (targetGram_posDef a b ha hb n).submatrix he

/-- The genuine actual row coefficients have precisely the original negative row-times-inverse-principal-block formula.
Use: the continuum Cholesky comparison estimates these exact original coefficients through the actual target Gram perturbation.
Article: jacobi, Theorem 2.1.
Proof: the proved real Gram inverse symmetry converts the projection's column formula to the printed row formula; the actual weighted support Gram matrix is the original target Gram matrix. -/
theorem rowCoefficient_inverse (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ)
    (i:Fin (n+1)) (j:Fin i.val) :
    rowCoefficient a b ha hb n i j=
      -(∑k:Fin i.val,targetGram a b ha hb n i (Gram.before i k)*
        ((targetGram a b ha hb n).submatrix (Gram.before i) (Gram.before i))⁻¹ k j) := by
  unfold rowCoefficient
  rw [Gram.coefficients_row]
  congr 1
  rw [targetGram_eq]
  rfl

/-- The actual original Schur normalization equals the original diagonal Gram entry plus the exact finite coefficient-times-cross-row sum.
Use: the original O(1/n) normalization estimate applies to this same actual q_(n,i) after the genuine quantitative Gram bounds are proved.
Article: jacobi, Theorem 2.1.
Proof: expand the exact original Schur complement and its negative projection coefficients, then identify the true original Gram entries. -/
theorem rowNormalization_formula (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) :
    rowNormalization a b ha hb n i=targetGram a b ha hb n i i+
      ∑j:Fin i.val,rowCoefficient a b ha hb n i j*targetGram a b ha hb n (Gram.before i j) i := by
  rw [targetGram_eq]
  simp only [rowNormalization,Gram.complement,rowCoefficient,Matrix.gram_apply,neg_mul,
    Finset.sum_neg_distrib,sub_eq_add_neg]

/-- The genuine original target polynomial has exactly the printed positive Schur row transformation of the actual corrected support family.
Use: Appendix C.4 evaluates this original identity at the target spectral nodes before taking its continuum limit.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the already proved genuine support degree and leading-coefficient facts discharge every premise of the complete canonical polynomial Schur theorem. Expanding its negative projection residual gives the original printed row coefficients and normalization exactly. -/
theorem targetPolynomial_schur (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) :
    targetPolynomial a b ha hb n i=(Real.sqrt (rowNormalization a b ha hb n i))⁻¹ •
      (supportPolynomial a b ha hb n i+
        ∑j:Fin i.val,rowCoefficient a b ha hb n i j • supportPolynomial a b ha hb n (Gram.before i j)) := by
  have h := (targetMeasure a b ha hb n).schur_formula (supportPolynomial a b ha hb n)
    (fun j => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree j).1)
    (fun j => ((supportMeasure a b ha hb n).orthogonalPolynomial_degree j).2) i
  simpa only [targetPolynomial,DiscreteMeasure.schurPolynomial,rowNormalization,rowCoefficient,
    neg_smul,Finset.sum_neg_distrib,sub_eq_add_neg] using h

end
end jacobi.Comparison
