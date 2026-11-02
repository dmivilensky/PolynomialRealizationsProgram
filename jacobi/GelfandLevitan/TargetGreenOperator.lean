import jacobi.GelfandLevitan.TargetSpectralOperator
import jacobi.Bessel.EdgeData
import chebyshev2.Continuum.DiagonalOperator

/-!
Article: jacobi, Theorem 2.1.
The summable original inverse sigma spectrum defines a genuine bounded
compact positive operator on the full physical L2 space. Both inverse
identities with the actual unbounded H_alpha hold on their full domains.
Identification with the continuous spatial Green kernel additionally
uses the separately required midpoint boundary matching.
Use: targetGreenOperator is an actual norm-convergent nuclear operator series, and its basis eigenvalues are the original 1/sigma_k.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine reciprocal target spectrum is absolutely summable.
Use: targetGreenOperator is an actual norm-convergent nuclear operator series, and its basis eigenvalues are the original 1/sigma_k.
Article: jacobi, Theorem 2.1.
Proof: the actual original Lambda_k=2/sigma_k are already proved positive and summable; divide their genuine series by two. -/
theorem target_inverse_spectrum_summable (a : ℝ) (ha : -1<a) :
    Summable (fun k => |(jacobi.Bessel.sigma a ha k)⁻¹|) := by
  have h := (jacobi.Bessel.edgeValue_summable ha).div_const 2
  have he : (fun k => |(jacobi.Bessel.sigma a ha k)⁻¹|)=
      (fun k => jacobi.Bessel.edgeValue a ha k/2) := by
    funext k
    rw [abs_of_pos (inv_pos.mpr (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k))),
      jacobi.Bessel.edgeValue,div_div_cancel_left' (by norm_num : (2:ℝ)≠0)]
  rw [he]
  exact h

/-- The original full bounded target Green inverse, built from the actual complete reflected transformed basis.
Use: targetOperator_green_inverse and targetGreen_operator_inverse prove the two genuine full-domain inverse identities for H_alpha.
Article: jacobi, Proposition C.2.
-/
def targetGreenOperator (a : ℝ) (ha : -1<a) : Space →L[ℝ] Space :=
  chebyshev2.Continuum.diagonalOperator (fullTargetBasis a ha)
    (fun k => (jacobi.Bessel.sigma a ha k)⁻¹)

/-- The original bounded Green operator has exactly the genuine inverse target eigenvalues on the unchanged actual reflected u basis.
Use: targetGreen_coordinates and both actual full-domain inverse identities follow from this original basis action.
Article: jacobi, Proposition C.2.
Proof: the earlier bounded diagonal series theorem applies because absolute summability of the genuine inverse sigma spectrum has been proved. -/
theorem targetGreen_basis (a : ℝ) (ha : -1<a) (k : ℕ) :
    targetGreenOperator a ha (fullTargetBasis a ha k)=
      (jacobi.Bessel.sigma a ha k)⁻¹ • fullTargetBasis a ha k :=
  chebyshev2.Continuum.diagonalOperator_basis _ (target_inverse_spectrum_summable a ha) k

/-- The full original bounded Green operator is positive in the community operator sense.
Use: targetGreen_coordinates uses its actual symmetry to compute all basis coefficients on arbitrary original L2 inputs.
Article: jacobi, Theorem 2.1.
Proof: reuse the earlier positive diagonal operator theorem for the actual complete basis and positive genuine inverse eigenvalues. -/
theorem targetGreen_positive (a : ℝ) (ha : -1<a) : (targetGreenOperator a ha).IsPositive :=
  chebyshev2.Continuum.diagonalOperator_positive _ (target_inverse_spectrum_summable a ha)
    (fun k => (inv_pos.mpr (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k))).le)

/-- The genuine bounded Green inverse is compact on the full original physical L2 space.
Use: gives the actual compact inverse assertion in the full target spectral realization.
Article: jacobi, Proposition C.2.
Proof: absolute summability of the original inverse eigenvalues makes the actual rank-one operator series a norm limit of finite-rank compact operators, by the earlier article's theorem. -/
theorem targetGreen_compact (a : ℝ) (ha : -1<a) : IsCompactOperator (targetGreenOperator a ha) :=
  chebyshev2.Continuum.diagonalOperator_isCompact _ (target_inverse_spectrum_summable a ha)

/-- Every original full L2 input has the exact reciprocal-spectrum coefficient formula under the genuine bounded Green operator.
Use: targetGreen_mem and the two original inverse identities are checked on all coordinates of the complete actual target basis.
Article: jacobi, Theorem 2.1.
Proof: move the actual symmetric Green operator onto the genuine basis vector and insert its independently proved inverse-sigma basis action. -/
theorem targetGreen_coordinates (a : ℝ) (ha : -1<a) (v : Space) (k : ℕ) :
    (fullTargetBasis a ha).repr (targetGreenOperator a ha v) k=
      (jacobi.Bessel.sigma a ha k)⁻¹*(fullTargetBasis a ha).repr v k := by
  calc
    _ = inner ℝ (fullTargetBasis a ha k) (targetGreenOperator a ha v) :=
      (fullTargetBasis a ha).repr_apply_apply _ _
    _ = inner ℝ (targetGreenOperator a ha (fullTargetBasis a ha k)) v :=
      ((targetGreen_positive a ha).1 (fullTargetBasis a ha k) v).symm
    _ = (jacobi.Bessel.sigma a ha k)⁻¹*inner ℝ (fullTargetBasis a ha k) v := by
      rw [targetGreen_basis,real_inner_smul_left]
    _ = _ := by rw [(fullTargetBasis a ha).repr_apply_apply]

/-- The actual full bounded Green operator maps every original L2 input into the full unbounded target domain.
Use: targetOperator_green_inverse is the actual H_alpha*H_alpha^(-1)=I identity on the entire original Hilbert space.
Article: jacobi, Theorem 2.1.
Proof: the full diagonal graph has the original input itself as a witness, because multiplication by sigma_k cancels each actual reciprocal Green coefficient. -/
theorem targetGreen_mem (a : ℝ) (ha : -1<a) (v : Space) :
    targetGreenOperator a ha v∈(targetOperator a ha).domain := by
  refine ⟨v,fun k => ?_⟩
  rw [targetGreen_coordinates,← mul_assoc,mul_inv_cancel₀
    (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)).ne',one_mul]

/-- The actual original unbounded target operator composed with its genuine bounded Green inverse is the identity on all original full-interval L2 inputs.
Use: establishes the first full-domain inverse assertion of Proposition C.2, beyond eigenvector or finite-sum identities.
Article: jacobi, Theorem 2.1.
Proof: compare every coefficient in the complete actual target basis using the true unbounded graph and proved reciprocal coefficient formula. -/
theorem targetOperator_green_inverse (a : ℝ) (ha : -1<a) (v : Space) :
    targetOperator a ha ⟨targetGreenOperator a ha v,targetGreen_mem a ha v⟩=v := by
  -- The full graph fixes every actual output coordinate; the genuine positive spectral denominators cancel those of the Green image.
  apply (fullTargetBasis a ha).repr.injective
  apply lp.ext
  apply funext
  intro k
  have h := chebyshev2.Continuum.unboundedDiagonalOperator_graph
    (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha) ⟨targetGreenOperator a ha v,targetGreen_mem a ha v⟩ k
  change (fullTargetBasis a ha).repr (targetOperator a ha ⟨targetGreenOperator a ha v,targetGreen_mem a ha v⟩) k=_ at h
  rw [h,targetGreen_coordinates,
    ← mul_assoc,mul_inv_cancel₀ (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)).ne',one_mul]

/-- The genuine bounded Green inverse composed with the actual unbounded H_alpha is the identity on its entire original graph domain.
Use: completes the genuine two-sided inverse statement in the full target spectral realization of Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: the actual Green coefficient formula and the full unbounded graph cancel the same genuine nonzero sigma_k at every original basis coordinate. -/
theorem targetGreen_operator_inverse (a : ℝ) (ha : -1<a) (v : (targetOperator a ha).domain) :
    targetGreenOperator a ha (targetOperator a ha v)=(v:Space) := by
  -- On the genuine entire graph domain, every spectral coefficient of H(v) has the actual sigma factor cancelled by its reciprocal Green multiplier.
  apply (fullTargetBasis a ha).repr.injective
  apply lp.ext
  apply funext
  intro k
  have h := chebyshev2.Continuum.unboundedDiagonalOperator_graph
    (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha) v k
  change (fullTargetBasis a ha).repr (targetOperator a ha v) k=_ at h
  rw [targetGreen_coordinates,h,
    ← mul_assoc,inv_mul_cancel₀ (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)).ne',one_mul]

end
end jacobi.GelfandLevitan
