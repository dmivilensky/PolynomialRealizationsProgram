import jacobi.GelfandLevitan.NormalizedReferencePerturbation
import jacobi.GelfandLevitan.TransformedParityFrame

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
The normalized original target reference vectors are a genuinely
norm-summable perturbation of each actual half-reference basis.
Their images under the true invertible GL transformation are the
actual normalized transformed vectors, with exact frame norm one.
Use: the compact perturbation of the actual half-reference basis maps its k-th vector to this true g_k.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The original normalized target reference vectors on the actual half-interval Hilbert space.
Use: the compact perturbation of the actual half-reference basis maps its k-th vector to this true g_k.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def normalizedSourceVector (a : ℝ) (ha : -1<a) (k : ℕ) : halfSubspace :=
  rowEmbedding (normalizedSourceMap a ha k)

/-- The actual normalized transformed waves in each original physical parity class.
Use: the unitary image of the original half-reference basis is identified with these genuine source functions.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def normalizedTransformedVector (a : ℝ) (ha : -1<a) (k : ℕ) : halfSubspace :=
  (halfNormalization a k*Real.sqrt (normingRatio a ha k)) •
    transformedVector a ha (jacobi.Bessel.sigma a ha k)

/-- The original normalized reference continuous function embeds as the actual complete half-reference basis entry.
Use: turns the independently proved continuous reference perturbation bound into a perturbation of the actual halfReferenceBasis.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: test the actual two Hilbert vectors against an arbitrary supported input. The continuous embedding gives the original reference coefficient integral, and the actual half-basis coefficient has the identical printed normalization. -/
theorem normalizedReferenceMap_vector (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    rowEmbedding (normalizedReferenceMap a ha (parityIndex p k))=halfReferenceBasis a ha p k := by
  -- Pairing with every genuine supported input identifies these original L2 quotient vectors without point evaluation.
  apply ext_inner_right ℝ
  intro v
  rw [normalizedReferenceMap,map_smul]
  change inner ℝ (halfNormalization a (parityIndex p k) •
    coefficientVector a ha (eigenvalue a (parityIndex p k))) v=_
  rw [halfReferenceBasis_apply,
    real_inner_smul_left (coefficientVector a ha (eigenvalue a (parityIndex p k))) v (halfNormalization a (parityIndex p k)),
    coefficientVector_inner,halfReferenceVector_inner]
  rfl

/-- The true normalized reference perturbation is absolutely summable in the actual Hilbert norm.
Use: its parity subsequences generate the compact synthesis correction in the actual two-bases proof.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the actual continuous perturbation has the proved uniform inverse-square tail. Apply the genuine bounded row embedding to that same difference, and compare its norms with the convergent original inverse-square p-series. Every omitted finite initial segment is summable automatically. -/
theorem normalizedSourceVector_norm_difference_summable (a : ℝ) (ha : -1<a) :
    Summable (fun k => ‖normalizedSourceVector a ha k-rowEmbedding (normalizedReferenceMap a ha k)‖) := by
  -- This is absolute Hilbert-norm summability, stronger than a merely formal series convergence claim.
  obtain ⟨C,_,hb⟩ := normalized_reference_pointwise_bound a ha
  have hM : Summable (fun k:ℕ => (‖rowEmbedding‖*C)/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using
      (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left (‖rowEmbedding‖*C)
  apply hM.of_norm_bounded_eventually_nat
  filter_upwards [hb] with k hk
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  change ‖rowEmbedding (normalizedSourceMap a ha k)-rowEmbedding (normalizedReferenceMap a ha k)‖≤_
  rw [← map_sub]
  have hn : ‖normalizedSourceMap a ha k-normalizedReferenceMap a ha k‖≤C/(k+1:ℝ)^2 :=
    ((normalizedSourceMap a ha k-normalizedReferenceMap a ha k).norm_le (by positivity)).mpr hk
  exact (rowEmbedding.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (by ring))

/-- Each actual target reference parity family is a norm-summable perturbation of its genuine complete reference basis.
Use: supplies the true compact-synthesis hypothesis, with all original spectral estimates discharged, in Two orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: take the injective original parity subsequence of the independently proved full absolute norm difference and identify its actual reference entry. -/
theorem normalizedSourceVector_parity_summable (a : ℝ) (ha : -1<a) (p : Fin 2) :
    Summable (fun k => ‖normalizedSourceVector a ha (parityIndex p k)-halfReferenceBasis a ha p k‖) := by
  have h := (normalizedSourceVector_norm_difference_summable a ha).comp_injective
    (i := parityIndex p) (fun _ _ h => by unfold parityIndex at h; omega)
  simpa only [Function.comp_def,normalizedReferenceMap_vector] using h

/-- The true GL transformation sends each actual normalized target reference vector to its actual normalized transformed wave.
Use: identifies the compact synthesis transformation's unitary image with the precise functions claimed in Two orthonormal bases.
Article: jacobi, Theorem 2.1.
Proof: bounded linear maps preserve the genuine norming scalar; the independently proved original transformation identity sends the actual reference coefficient vector to the actual u vector. -/
theorem transformationPlus_normalizedSourceVector (a : ℝ) (ha : -1<a) (k : ℕ) :
    transformationPlus a ha (normalizedSourceVector a ha k)=normalizedTransformedVector a ha k := by
  rw [normalizedSourceVector,normalizedSourceMap,map_smul]
  change transformationPlus a ha ((halfNormalization a k*Real.sqrt (normingRatio a ha k)) •
    coefficientVector a ha (jacobi.Bessel.sigma a ha k))=_
  rw [map_smul,transformationPlus_coefficientVector]
  rfl

/-- The square of the original normalized target scalar is exactly twice its true norming weight.
Use: normalized_transformed_parity_parseval rewrites the proved original weighted frame as the actual squared-coefficient frame.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the actual positive square roots square to their original norm and ratio, and the original scalar factors multiply exactly. -/
theorem halfNormalization_weight_sq (a : ℝ) (ha : -1<a) (k : ℕ) :
    (halfNormalization a k*Real.sqrt (normingRatio a ha k))^2=
      2*normingRatio a ha k/norming a k := by
  rw [mul_pow,halfNormalization,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
    Real.sq_sqrt (norming_pos ha k).le,Real.sq_sqrt (normingRatio_properties ha k).2.le]
  ring

/-- Each actual normalized transformed parity system is a tight frame with exact constant one.
Use: once its true synthesis transformation is proved invertible, this identity forces unitarity and gives both actual orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: insert the genuine normalized transformed vectors in the independently proved original weighted frame identity and use the exact original scalar-square normalization. -/
theorem normalized_transformed_parity_parseval (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace) :
    HasSum (fun k => (inner ℝ (normalizedTransformedVector a ha (parityIndex p k)) v)^2) (‖v‖^2) := by
  apply (transformed_parity_parseval a ha p v).congr_fun
  intro k
  rw [normalizedTransformedVector,
    real_inner_smul_left (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k))) v
      (halfNormalization a (parityIndex p k)*Real.sqrt (normingRatio a ha (parityIndex p k))),
    mul_pow,halfNormalization_weight_sq]
  ring

end
end jacobi.GelfandLevitan
