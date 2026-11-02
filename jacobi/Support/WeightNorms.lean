import jacobi.Finite.ChristoffelWeights
import jacobi.Support.Polynomials

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The actual original support probabilities equal the reciprocals of
their complete squared original polynomial norms, both before and
after the genuine affine support correction.
Use: the genuine support edge weight limit follows by applying polynomial convergence to this exact normalization, with no independently assumed norming coefficient.
-/
namespace jacobi.Support
noncomputable section
open jacobi.Finite

/-- The reciprocal original natural support probability is exactly the full original squared spectral-polynomial norm.
Use: the genuine support edge weight limit follows by applying polynomial convergence to this exact normalization, with no independently assumed norming coefficient.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: identify every actual normalized support polynomial with the genuine canonical spectral polynomial and use the proved complete Christoffel norm identity. -/
theorem naturalMeasure_inverse_weight (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    ((naturalMeasure a b ha hb n).weight k)⁻¹=
      ∑i:Fin (n+1),((naturalPolynomial a b ha hb n i).eval (naturalNode a b (n+1) k))^2 := by
  simp_rw [naturalPolynomial_eq]
  exact (naturalMeasure a b ha hb n).inverse_weight_polynomial_norm k

/-- The reciprocal original corrected support probability is exactly its full original corrected squared spectral-polynomial norm.
Use: the target/support Gram comparison uses the genuine corrected support family and the same actual probability normalization as the natural edge limit.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: the corrected family is the actual canonical polynomial family of its original corrected spectral measure, so the same complete Christoffel identity applies. -/
theorem supportMeasure_inverse_weight (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (k:Fin (n+1)) :
    ((supportMeasure a b ha hb n).weight k)⁻¹=
      ∑i:Fin (n+1),((supportPolynomial a b ha hb n i).eval (jacobi.Jacobi.modelNode a b (n+1) k))^2 :=
  (supportMeasure a b ha hb n).inverse_weight_polynomial_norm k

end
end jacobi.Support
