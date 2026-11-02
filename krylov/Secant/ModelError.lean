import krylov.Secant.Canonical
import krylov.LinearAlgebra.LeastGain
import krylov.LinearAlgebra.MatrixNormBounds

/-!
Article: main_krylov, apG:mss, normalized latest-model error and the oldest diagonal.
Use: derive the actual model discrepancy, its dimension/conditioning estimate
and the exact rank-one oldest-pair split from the actual observed columns.
Source: the proved latest-information model and actual inverse-coordinate/dual-distance calculus.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- Actual normalized data error: latest observed pairings minus the true reference Gram matrix.
Use: its entries are the normalized observed operator deviations, with no assumed model-error field.
Article: main_krylov, apG:mss, X. -/
def normalizedDataError (V : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  latest (Vᵀ*pairImages V A)-Vᵀ*V

/-- The actual latest-data error entry uses precisely the newer of its two observed operators.
Use: connects X to the article's actual normalized column formula.
Article: main_krylov, apG:mss, X_ij=û_iᵀ(Â_max(i,j)−I)û_j.
Proof: apply the exact latest-observation identity to the actual compressed trajectory. -/
theorem normalizedDataError_entry (V : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k, (A k).IsSymm) (i j : Fin n) :
    normalizedDataError V A i j=(Vᵀ*(A (max i.val j.val)-1)*V) i j := by
  have hc (k : ℕ) : (Vᵀ*A k*V).IsSymm := by
    simp only [Matrix.IsSymm, transpose_mul, transpose_transpose, (hA k).eq, Matrix.mul_assoc]
  rw [normalizedDataError, ← observed_compression, Matrix.sub_apply, latest_observed_apply _ hc]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rfl

/-- The actual inverse congruence of the actual column Gram matrix is the identity.
Use: subtract the true base from the observed ambient model without an assumed whitening identity.
Article: main_krylov, apG:mss, normalized base cancellation.
Proof: cancel each actual coordinate matrix against its own inverse. -/
theorem inverseCongruence_gram (V : Matrix (Fin n) (Fin n) ℝ) (hV : IsUnit V.det) :
    inverseCongruence V (Vᵀ*V)=1 := by
  have ht : IsUnit Vᵀ.det := by simpa only [det_transpose] using hV
  simp only [inverseCongruence, ← Matrix.mul_assoc, nonsing_inv_mul _ ht,
    Matrix.one_mul, mul_nonsing_inv _ hV]

/-- The actual latest-information ambient model error is exactly the inverse congruence of actual X.
Use: proves the source model identity directly from its observed data.
Article: main_krylov, apG:mss, Ĵ−I=Û^(−T)XÛ⁻¹.
Proof: distribute the actual inverse congruence and cancel the actual reference Gram matrix. -/
theorem normalized_model_error (V : Matrix (Fin n) (Fin n) ℝ) (hV : IsUnit V.det)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    inverseCongruence V (latest (Vᵀ*pairImages V A))-1 =
      inverseCongruence V (normalizedDataError V A) := by
  rw [normalizedDataError]
  simp only [inverseCongruence, Matrix.mul_sub, Matrix.sub_mul]
  change inverseCongruence V (latest (Vᵀ*pairImages V A))-1 =
    inverseCongruence V (latest (Vᵀ*pairImages V A))-inverseCongruence V (Vᵀ*V)
  rw [inverseCongruence_gram V hV]

/-- Genuine inverse congruence has its actual squared inverse-norm bound.
Use: both the total and newer-pair remainder have their correct conditioning amplification.
Article: main_krylov, apG:mss, σ⁻²‖X‖.
Proof: multiply genuine spectral norms and use norm invariance under actual transposition. -/
theorem inverseCongruence_norm (V X : Matrix (Fin n) (Fin n) ℝ) :
    ‖inverseCongruence V X‖≤‖V⁻¹‖^2*‖X‖ := by
  have ht : ‖Vᵀ⁻¹‖=‖V⁻¹‖ := by
    rw [← transpose_nonsing_inv]
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose V⁻¹
  calc
    _ ≤ ‖Vᵀ⁻¹‖*‖X‖*‖V⁻¹‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by rw [ht]; ring

/-- The actual entry pairing of an actual compressed form is its genuine Euclidean inner product.
Use: unit normalized columns bound X entries by the real operator budget.
Article: main_krylov, apG:mss, normalized entry bound.
Proof: associate the actual matrix products and expand their common finite scalar pairing. -/
theorem compressed_entry_pairing (V E : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Vᵀ*E*V) i j = inner ℝ (WithLp.toLp 2 (fun a => V a i))
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E (WithLp.toLp 2 (fun a => V a j))) := by
  rw [Matrix.inner_toEuclideanCLM, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, Matrix.mulVec]

/-- The actual normalized model satisfies the printed n-times operator-budget bound.
Use: instantiate ε with the finite maximum of the actual normalized operator deviations.
Article: main_krylov, apG:mss, ‖Ĵ−I‖≤n max_i‖Â_i−I‖/σ².
Proof: true unit column pairings bound every actual X entry; the proved
Frobenius comparison gives nε, and actual inverse congruence gives the squared inverse factor. -/
theorem normalized_model_bound (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hV : IsUnit V.det)
    (A : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : ∀ k, (A k).IsSymm)
    (hcol : ∀ i, ‖euclideanColumn V i‖=1) {ε : ℝ} (hε : 0≤ε)
    (hbudget : ∀ k<n+1, ‖A k-1‖≤ε) :
    ‖inverseCongruence V (latest (Vᵀ*pairImages V A))-1‖≤(n+1)*ε/(leastGain V)^2 := by
  -- Bound the true observed entries before comparing the actual Frobenius and spectral norms.
  have he (i j : Fin (n+1)) : |normalizedDataError V A i j|≤ε := by
    rw [normalizedDataError_entry V A hA, compressed_entry_pairing]
    have hc := norm_inner_le_norm (𝕜 := ℝ) (euclideanColumn V i)
      (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (A (max i.val j.val)-1) (euclideanColumn V j))
    have ho := (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (A (max i.val j.val)-1)).le_opNorm
      (euclideanColumn V j)
    simp only [hcol, one_mul, mul_one, Real.norm_eq_abs, Matrix.l2_opNorm_toEuclideanCLM] at hc ho
    exact hc.trans (ho.trans (hbudget _ (max_lt i.isLt j.isLt)))
  have hx := (spectral_le_hsNorm (normalizedDataError V A)).trans
    (hsNorm_le_dimension _ hε he)
  rw [normalized_model_error V hV]
  have hi := inverseCongruence_norm V (normalizedDataError V A)
  have hh := hi.trans (mul_le_mul_of_nonneg_left hx (sq_nonneg _))
  convert hh using 1
  simp only [leastGain, inv_pow, inv_inv, div_eq_mul_inv]
  push_cast
  ring

/-- The actual oldest coordinate rank-one term transforms to the actual oldest dual outer product.
Use: separates the oldest-pair diagonal from all other normalized errors.
Article: main_krylov, apG:mss, X₀₀bbᵀ.
Proof: multiply the actual outer product on both sides and transpose its actual inverse action. -/
theorem inverseCongruence_oldest (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    inverseCongruence V (vecMulVec (Pi.single 0 1) (Pi.single 0 1)) =
      vecMulVec (WithLp.ofLp (oldestDual V)) (WithLp.ofLp (oldestDual V)) := by
  simp only [inverseCongruence, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, oldestDual]
  congr 1
  rw [← transpose_nonsing_inv, mulVec_transpose]

/-- The actual normalized error has precisely its oldest rank-one component and actual remainder.
Use: all diagonal isolation is an identity of the actual computed model, not a hypothesis on its error.
Article: main_krylov, apG:mss, oldest-pair decomposition.
Proof: split X into its actual oldest entry and the actual remaining entries,
then distribute the actual congruence and use the proved dual outer-product identity. -/
theorem oldest_model_split (V X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    inverseCongruence V X = X 0 0 • vecMulVec (WithLp.ofLp (oldestDual V)) (WithLp.ofLp (oldestDual V))+
      inverseCongruence V (X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)) := by
  have he := inverseCongruence_oldest V
  simp only [inverseCongruence, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] at *
  rw [he]
  abel

end
end krylov.Secant
