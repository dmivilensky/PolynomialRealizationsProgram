import jacobi.Finite.SpectralPolynomial
import jacobi.Finite.Reconstruction

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
Use: supportPolynomial uses the literal three-term recurrence, while normalizedLeading_eq_orthogonalPolynomial identifies it with the actual spectral orthogonal family in the Gram comparison.
-/
namespace jacobi.Finite
noncomputable section
open Real Matrix Polynomial chebyshev1 chebyshev2
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The original recurrence polynomial with its genuine positive coupling-product normalization.
Use: supportPolynomial uses the literal three-term recurrence, while normalizedLeading_eq_orthogonalPolynomial identifies it with the actual spectral orthogonal family in the Gram comparison.
Article: jacobi, Appendix C.3 (top-node polynomials).
-/
def normalizedLeading {n : ℕ} (J : Jacobi n) (m : ℕ) : ℝ[X] :=
  C (J.data.linkProduct m)⁻¹*J.data.leading m

/-- Every actual original interior coupling product is strictly positive for an irreducible genuine finite Jacobi chain.
Use: normalizedLeading_eq_orthogonalPolynomial and the support recurrence divide only by genuine nonzero original factors.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: every used original adjacent squared coupling is strictly positive, so every genuine square root in the original finite product is positive. -/
theorem linkProduct_pos {n : ℕ} {J : Jacobi n} (hJ:J.Irreducible) {m : ℕ} (hm:m<n) :
    0<J.data.linkProduct m := by
  unfold JacobiData.linkProduct
  apply Finset.prod_pos
  intro k hk
  have hk' := Finset.mem_range.mp hk
  exact Real.sqrt_pos.mpr (hJ (k+1) (by omega) (by omega))

/-- The genuine original normalized recurrence polynomial has at most its actual original recurrence degree.
Use: equality of actual weighted spectral evaluations identifies it with the independently constructed canonical polynomial.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: multiplying the original monic leading continuant by its genuine constant normalization does not increase its already proved degree. -/
theorem normalizedLeading_degree_le {n : ℕ} (J : Jacobi n) (m : ℕ) :
    (normalizedLeading J m).natDegree≤m := by
  unfold normalizedLeading
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact le_of_eq (J.data.block_natDegree J.coupling_nonneg 0 m)

/-- The original normalized leading recurrence polynomial is exactly the genuine canonical orthogonal polynomial of the same actual finite spectral measure.
Use: the support top-node product and Volterra recurrence concern the same actual polynomials used in the target-measure Gram matrix and Cholesky limit.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the already proved genuine leading-site spectral identity evaluates the original recurrence polynomial in the actual reconstructed eigenbasis. Its true positive first row is sqrt(weight), and its original coupling product is nonzero. Thus its weighted evaluation equals the actual canonical polynomial-basis vector. The original degree bounds make evaluation injective, giving equality as actual polynomials. -/
theorem normalizedLeading_eq_orthogonalPolynomial {n : ℕ} (M:DiscreteMeasure n) (i:Fin n) :
    normalizedLeading M.reconstructed i=M.orthogonalPolynomial i := by
  -- The original spectral vector identity retains its sign; equality is not inferred merely from matching squared wave amplitudes.
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hp := linkProduct_pos M.reconstructed_irreducible i.isLt
  apply M.evaluate_injective ((normalizedLeading_degree_le _ _).trans_lt i.isLt)
    (by rw [(M.orthogonalPolynomial_degree i).1]; exact i.isLt)
  rw [M.evaluate_orthogonalPolynomial]
  apply PiLp.ext
  intro k
  have h := spectral_leading_values M.reconstructed M.reconstructedBasis hn i.isLt k
  change (M.reconstructed.data.leading i).eval (M.node k)*M.eigenvectors ⟨0,hn⟩ k=
    M.reconstructed.data.linkProduct i*M.eigenvectors i k at h
  rw [M.eigenvectors_first hn] at h
  change Real.sqrt (M.weight k)*(normalizedLeading M.reconstructed i).eval (M.node k)=M.eigenvectors i k
  rw [normalizedLeading,Polynomial.eval_mul,Polynomial.eval_C]
  field_simp [hp.ne']
  linear_combination h

end
end jacobi.Finite
