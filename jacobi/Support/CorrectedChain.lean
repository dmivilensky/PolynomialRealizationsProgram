import jacobi.Support.Spectrum
import jacobi.Support.AffineScale
import jacobi.Finite.AffineSpectrum

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The actual corrected support chain has the literal affine matrix, exact
original corrected model spectrum and genuine physical persymmetry.
The original natural eigenvectors give its actual unchanged spectral
basis; no contractivity of the corrected support spectrum is assumed.
Use: its actual polynomial system and spectral weights are compared with those of the target Jacobi fibre in the original Gram limit.
-/
namespace jacobi.Support
noncomputable section
open Real Matrix Polynomial jacobi.Reference jacobi.Finite chebyshev2 chebyshev1

/-- The original corrected support Jacobi chain with the literal original two-edge scale and shift.
Use: its actual polynomial system and spectral weights are compared with those of the target Jacobi fibre in the original Gram limit.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
-/
def supportChain (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : Jacobi n :=
  affine (naturalChain a b ha hb n) (jacobi.Jacobi.modelScale a b n) (jacobi.Jacobi.modelShift a b n)

/-- The corrected support encoding is exactly the original printed finite affine matrix at every genuine nonempty dimension.
Use: supportBasis and supportChain_persymmetric identify the actual original corrected finite chain.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the independently proved actual scale is positive, so the earlier genuine affine Jacobi matrix identity applies. -/
theorem supportChain_matrix (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) :
    (supportChain a b ha hb n).matrix= jacobi.Jacobi.modelScale a b n • (naturalChain a b ha hb n).matrix+
      Matrix.scalar (Fin n) (jacobi.Jacobi.modelShift a b n) :=
  affine_matrix _ (modelScale_pos ha hb hn).le _

/-- The actual corrected support chain is irreducible throughout the entire original parameter range and in every nonempty dimension.
Use: the original corrected support spectral measure has strictly positive weights at every genuine model node.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: actual natural irreducibility and the independently proved positive original affine scale preserve each genuine positive adjacent coupling. -/
theorem supportChain_irreducible (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) :
    (supportChain a b ha hb n).Irreducible :=
  affine_irreducible (naturalChain_irreducible a b ha hb n) (modelScale_pos ha hb hn).ne' _

/-- The actual original corrected support matrix is genuinely persymmetric.
Use: the support weight comparison uses the original reciprocal-characteristic-derivative weights of the same actual corrected matrix.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the actual natural matrix is persymmetric; a real scalar multiple and the original scalar identity shift preserve the exact same simultaneous row and column reversal. -/
theorem supportChain_persymmetric (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) :
    (supportChain a b ha hb n).matrix.submatrix Fin.rev Fin.rev=(supportChain a b ha hb n).matrix := by
  -- Every original corrected finite entry retains the genuine physical reversal, including the scalar diagonal shift.
  rw [supportChain_matrix a b ha hb hn]
  ext i j
  have h := congrArg (fun M:Matrix (Fin n) (Fin n) ℝ => M i j) (naturalChain_persymmetric a b ha hb n)
  change (naturalChain a b ha hb n).matrix i.rev j.rev=(naturalChain a b ha hb n).matrix i j at h
  simp only [Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.scalar_apply,Matrix.diagonal_apply,Fin.rev_injective.eq_iff,h]

/-- The genuine original natural support spectral basis, ordered by the original actual cosine nodes.
Use: supportBasis reuses its actual eigenvectors unchanged for the corrected support matrix, and support weights are its genuine first-row squared coordinates.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def naturalBasis (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    SpectralBasis (naturalChain a b ha hb n).matrix :=
  orderedBasis (naturalNodes a b ha hb n) (naturalChain a b ha hb n) (naturalChain_inFiber a b ha hb n)

/-- The actual natural spectral basis has exactly the original cosine-node values in the original enumeration.
Use: supportBasis_values proves the actual corrected support eigenvalue formula.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the earlier actual ordered-basis theorem applies to the independently proved original natural support fibre. -/
theorem naturalBasis_values (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (k:Fin n) :
    (naturalBasis a b ha hb n).eigenvalues k=naturalNode a b n k :=
  congrFun (orderedBasis_values _ _ _) k

/-- The actual ordered spectral basis of the original corrected support chain, with the natural physical eigenvectors retained unchanged.
Use: original support weights and orthogonal polynomial evaluations are the genuine spectral data of this actual matrix.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def supportBasis (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) :
    SpectralBasis (supportChain a b ha hb n).matrix :=
  affineBasis (naturalChain a b ha hb n) (naturalBasis a b ha hb n) (modelScale_pos ha hb hn).le _

/-- Every actual original corrected support eigenvalue is exactly its original corrected cosine model node eta_(n,k).
Use: supportChain_spectrum and the genuine target/support weight comparison use the actual source model nodes already controlled in Proposition B.1.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the actual affine basis has its genuine affine-image eigenvalues, and the original natural basis values are exactly the original cosine lattice. -/
theorem supportBasis_values (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) (k:Fin n) :
    (supportBasis a b ha hb hn).eigenvalues k= jacobi.Jacobi.modelNode a b n k := by
  rw [supportBasis,affineBasis_values,naturalBasis_values]
  rfl

/-- The entire actual corrected support characteristic polynomial is the original product of all genuine corrected model nodes.
Use: the original support weight ratios compare precisely the actual corrected support and target characteristic gaps.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the genuine corrected support spectral basis gives the actual full finite characteristic product, with its original model eigenvalues already identified. -/
theorem supportChain_charpoly (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) :
    (supportChain a b ha hb n).matrix.charpoly=∏ k:Fin n,(X-C (jacobi.Jacobi.modelNode a b n k)) := by
  rw [(supportBasis a b ha hb hn).charpoly_factor]
  simp only [supportBasis_values]

/-- The actual corrected original support matrix has exactly the article's entire corrected model spectrum throughout the full original parameter range.
Use: the discrete-to-continuum Gram comparison compares the same actual support chain with the actual Jacobi-zero target fibre.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: roots of the independently proved actual full characteristic product are precisely the original finite corrected model-node family. -/
theorem supportChain_spectrum (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) :
    spectrum ℝ (supportChain a b ha hb n).matrix=Set.range (fun k:Fin n => jacobi.Jacobi.modelNode a b n k) := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,supportChain_charpoly a b ha hb hn]
  simp only [Polynomial.IsRoot,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,sub_eq_zero,Set.mem_range]
  constructor <;> rintro ⟨k,hk⟩ <;> exact ⟨k,hk.symm⟩

end
end jacobi.Support
