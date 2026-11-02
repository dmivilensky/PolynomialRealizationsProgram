import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Finite Gram orthogonalization is supplied by mathlib, with its positive diagonal
and inverse change-of-basis formula proved explicitly here. Applying this to
weighted polynomial evaluation vectors yields the article's change of measure.
Source: mathlib, GramSchmidtOrtho and GramMatrix; finite Gram--Schmidt factorization.
Use: fixes the positive sign of the Cholesky diagonal.
-/

namespace jacobi.Finite.Gram
noncomputable section
open InnerProductSpace Matrix
open scoped InnerProductSpace BigOperators

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The diagonal Gram--Schmidt pairing is its squared residual norm.
Use: fixes the positive sign of the Cholesky diagonal.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: the earlier orthogonal vectors have zero pairing with the current residual. -/
theorem inner_residual (f : Fin N → E) (i : Fin N) :
    inner ℝ (gramSchmidt ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖^2 := by
  rw [gramSchmidt_def'' ℝ f i, inner_add_right]
  simp only [inner_sum, real_inner_self_eq_norm_sq]
  rw [Finset.sum_eq_zero (fun j hj => ?_), add_zero]
  simp only [inner_smul_right]
  rw [gramSchmidt_orthogonal ℝ f (ne_of_gt (Finset.mem_Iio.mp hj)), mul_zero]

variable [FiniteDimensional ℝ E]

/-- The normalized Gram--Schmidt basis in the ambient finite Hilbert space.
Use: gives the new orthonormal polynomial coordinates after changing measure.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def basis (h : Module.finrank ℝ E = Fintype.card (Fin N)) (f : Fin N → E) :
    OrthonormalBasis (Fin N) ℝ E := gramSchmidtOrthonormalBasis h f

/-- The lower triangular coordinates of the input vectors in the new basis.
Use: is the Cholesky factor of their Gram matrix.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def lower (h : Module.finrank ℝ E = Fintype.card (Fin N)) (f : Fin N → E) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => (basis h f).repr (f i) j

/-- Coordinates above the diagonal vanish.
Use: the inverse change of basis only involves preceding polynomial degrees.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: mathlib's Gram--Schmidt basis is orthogonal to all preceding inputs. -/
theorem lower_triangular (h : Module.finrank ℝ E = Fintype.card (Fin N)) (f : Fin N → E) :
    (lower h f).IsLowerTriangular := by
  intro i j hij
  exact gramSchmidtOrthonormalBasis_inv_triangular' h f hij

/-- The diagonal is the norm of the unnormalized orthogonal residual.
Use: proves positivity and fixes the leading-coefficient orientation.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: normalize the squared residual pairing by its nonzero norm. -/
theorem lower_diagonal (h : Module.finrank ℝ E = Fintype.card (Fin N))
    {f : Fin N → E} (hf : LinearIndependent ℝ f) (i : Fin N) :
    lower h f i i = ‖gramSchmidt ℝ f i‖ := by
  have hn := norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hf)
  have hi := (gramSchmidtNormed_linearIndependent hf).ne_zero i
  rw [lower, OrthonormalBasis.repr_apply_apply]
  rw [basis, gramSchmidtOrthonormalBasis_apply h hi]
  rw [gramSchmidtNormed, inner_smul_left, inner_residual]
  simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id_eq]
  field_simp [hn]

/-- The Gram matrix factors as L Lᵀ.
Use: supplies the actual Cholesky factor, rather than assuming its existence.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: Parseval's finite identity in the orthonormal Gram--Schmidt basis. -/
theorem factorization (h : Module.finrank ℝ E = Fintype.card (Fin N)) (f : Fin N → E) :
    Matrix.gram ℝ f = lower h f * (lower h f)ᵀ := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, lower,
    OrthonormalBasis.repr_apply_apply]
  simpa only [real_inner_comm] using ((basis h f).sum_inner_mul_inner (f i) (f j)).symm

/-- The triangular factor is invertible and has a strictly positive diagonal.
Use: justifies its matrix inverse in the polynomial transformation.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: independent inputs give nonzero residuals and a positive determinant product. -/
theorem lower_invertible (h : Module.finrank ℝ E = Fintype.card (Fin N))
    {f : Fin N → E} (hf : LinearIndependent ℝ f) :
    IsUnit (lower h f).det ∧ ∀ i, 0 < lower h f i i := by
  have hp (i : Fin N) : 0 < lower h f i i := by
    rw [lower_diagonal h hf i]
    exact norm_pos_iff.mpr (gramSchmidt_ne_zero i hf)
  refine ⟨isUnit_iff_ne_zero.mpr ?_, hp⟩
  rw [Matrix.det_of_isLowerTriangular _ (lower_triangular h f)]
  exact ne_of_gt (Finset.prod_pos (fun i _ => hp i))

/-- The inverse triangular factor reconstructs every orthonormalized vector.
Use: specializes to ψᵢ = ∑ⱼ (L⁻¹)ᵢⱼ ψⱼ⁰ in the changed discrete measure.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: expand the original vectors in the orthonormal basis and multiply by L⁻¹. -/
theorem inverse_coordinates (h : Module.finrank ℝ E = Fintype.card (Fin N))
    {f : Fin N → E} (hf : LinearIndependent ℝ f) (i : Fin N) :
    basis h f i = ∑ j, (lower h f)⁻¹ i j • f j := by
  -- Apply the orthonormal coordinate isomorphism, where the claim is the inverse matrix identity.
  apply (basis h f).repr.injective
  apply PiLp.ext
  intro k
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    OrthonormalBasis.repr_self]
  change (EuclideanSpace.single i (1 : ℝ)) k =
    ∑ j, (lower h f)⁻¹ i j * lower h f j k
  rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (lower_invertible h hf).1]
  simp [Matrix.one_apply, eq_comm]

/-- The inverse Cholesky factor is lower triangular as well.
Use: the transformed polynomial in row i has no term of degree above i.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: apply the community inverse theorem for block triangular matrices. -/
theorem inverse_lower_triangular (h : Module.finrank ℝ E = Fintype.card (Fin N))
    {f : Fin N → E} (hf : LinearIndependent ℝ f) :
    ((lower h f)⁻¹).IsLowerTriangular := by
  let := Matrix.invertibleOfIsUnitDet _ (lower_invertible h hf).1
  exact Matrix.blockTriangular_inv_of_blockTriangular (lower_triangular h f)

/-- Each inverse diagonal entry is the reciprocal of the positive Cholesky diagonal.
Use: proves that transformed polynomials retain positive leading coefficients.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: in the diagonal entry of L⁻¹L every off-diagonal summand vanishes. -/
theorem inverse_diagonal (h : Module.finrank ℝ E = Fintype.card (Fin N))
    {f : Fin N → E} (hf : LinearIndependent ℝ f) (i : Fin N) :
    (lower h f)⁻¹ i i = (lower h f i i)⁻¹ := by
  -- All off-diagonal terms in this diagonal matrix-product entry vanish by the two triangularity statements.
  have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i i)
    (Matrix.nonsing_inv_mul _ (lower_invertible h hf).1)
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at he
  · simpa only [one_div] using (eq_div_iff ((lower_invertible h hf).2 i).ne').mpr he
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [lower_triangular h f hj, mul_zero]
    · rw [inverse_lower_triangular h hf hj, zero_mul]
  · simp

end
end jacobi.Finite.Gram
