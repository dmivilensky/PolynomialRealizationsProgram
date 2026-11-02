import krylov.LinearAlgebra.Compression
import krylov.LinearAlgebra.NormalizedRankOne
import Mathlib.Analysis.Matrix.Hermitian

/-!
Article: main_krylov, apA:galerkin(c), the actual finite-matrix compression inequality.
Use: the proved Hilbert compression is applied to the original symmetric idempotent
matrix, with its actual old-subspace range and genuine Euclidean matrix norm.
Source: mathlib's symmetric-projection/range equivalence and the proved compression theorem.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- An actual symmetric idempotent matrix is exactly the orthogonal projection onto an actual subspace.
Use: discharge the old-subspace premise for the finite matrices appearing in the article.
Article: main_krylov, apA:galerkin(c), orthogonal P.
Proof: transfer actual idempotence and symmetry through the matrix/operator equivalence,
then reuse mathlib's proved projection-on-range characterization. -/
theorem matrix_projection_representation (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hPid : P * P = P) :
    ∃ (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (_ : K.HasOrthogonalProjection),
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P = K.starProjection := by
  let p := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P
  have hi : IsIdempotentElem p := by
    change p * p = p
    have h := congrArg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) hPid
    simpa only [p, map_mul] using h
  have hs : p.toLinearMap.IsSymmetric := by
    change (Matrix.toEuclideanLin P).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hP)
  -- The subspace is constructed as the actual range by the existing projection theorem.
  have hil : IsIdempotentElem p.toLinearMap := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T v) hi
  obtain ⟨K, hK, he⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection.mp ⟨hil, hs⟩
  let : K.HasOrthogonalProjection := hK
  refine ⟨K, hK, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => T v) he

/-- The genuine Euclidean squared action is the physical transpose-product quadratic form.
Use: translate actual Hilbert compression energies into the source Loewner matrix inequality.
Article: main_krylov, apA:galerkin(c).
Proof: move the actual matrix through the real pairing and associate its two actions. -/
theorem matrix_action_norm_sq (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 (M *ᵥ v)‖^2 = v ⬝ᵥ ((Mᵀ * M) *ᵥ v) := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial,
    transpose_pairing, mulVec_mulVec]

/-- The actual matrices P,E,e satisfy the exact printed positive-semidefinite compression bound.
Use: no abstract projection or hypothetical quadratic-form model remains in Y²+xxᵀ≤ω²P.
Article: main_krylov, apA:galerkin(c), first displayed matrix inequality.
Proof: construct the actual range projection, apply the proved Hilbert compression
to every physical input vector, and identify its genuine action energies with matrix quadratic forms. -/
theorem matrix_compression_order (P E : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hPid : P * P = P) (hE : E.IsSymm)
    (e : Fin n → ℝ) (he : P *ᵥ e = 0) (hen : ‖WithLp.toLp 2 e‖ = 1)
    {ω : ℝ} (hω : chebyshev1.opNorm E ≤ ω) :
    let Y := P * E * P
    let x := P *ᵥ (E *ᵥ e)
    Y^2 + vecMulVec x x ≤ ω^2 • P := by
  dsimp only
  let Y := P * E * P
  let x := P *ᵥ (E *ᵥ e)
  have hY : Y.IsSymm := by
    simp only [Y, Matrix.IsSymm, transpose_mul, hP.eq, hE.eq, Matrix.mul_assoc]
  have hxx : (vecMulVec x x).IsHermitian := by
    simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star x).1
  have hysq : (Y^2).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (hY.pow 2)
  have ht : IsSelfAdjoint (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    change (Matrix.toEuclideanLin E).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hE)
  obtain ⟨K, hK, hproj⟩ := matrix_projection_representation P hP hPid
  let : K.HasOrthogonalProjection := hK
  have heK : WithLp.toLp 2 e ∈ Kᗮ := by
    apply K.starProjection_apply_eq_zero_iff.mp
    rw [← hproj, Matrix.toEuclideanCLM_toLp, he]
    rfl
  change (ω^2 • P - (Y^2 + vecMulVec x x)).PosSemidef
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_iff_isSymm.mpr hP).smul (show IsSelfAdjoint (ω^2) from rfl) |>.sub (hysq.add hxx))
  intro v
  -- The proved actual projection inequality is tested on the same physical vector v.
  have hc := compression_quadratic K (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E) ht hω
    (WithLp.toLp 2 e) heK hen (WithLp.toLp 2 v)
  rw [← hproj] at hc
  simp only [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, star_trivial] at hc
  have hpn : ‖WithLp.toLp 2 (P *ᵥ v)‖^2 = v ⬝ᵥ (P *ᵥ v) := by
    rw [matrix_action_norm_sq, hP.eq, hPid]
  have hyn : ‖WithLp.toLp 2 (P *ᵥ (E *ᵥ (P *ᵥ v)))‖^2 = v ⬝ᵥ ((Y^2) *ᵥ v) := by
    rw [mulVec_mulVec, mulVec_mulVec]
    change ‖WithLp.toLp 2 (Y *ᵥ v)‖^2 = _
    rw [matrix_action_norm_sq, hY.eq, pow_two]
  rw [hpn, hyn] at hc
  simp only [star_trivial, sub_mulVec, smul_mulVec, add_mulVec,
    krylov.Secant.outer_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hpair : x ⬝ᵥ v = v ⬝ᵥ x := dotProduct_comm x v
  change v ⬝ᵥ ((Y^2) *ᵥ v) + (v ⬝ᵥ x)^2 ≤ ω^2 * (v ⬝ᵥ (P *ᵥ v)) at hc
  rw [hpair]
  nlinarith

/-- The actual finite matrices satisfy the sharp compressed action inequality for every physical vector.
Use: completes the finite-matrix specialization of both source compression conclusions.
Article: main_krylov, apA:galerkin(c), ‖YX‖²≤ω²‖X‖²−(xᵀX)².
Proof: evaluate the proved actual Loewner bound on v, identify its squared
actions, and use contractivity of the same actual orthogonal projection. -/
theorem matrix_compression_action (P E : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hPid : P * P = P) (hE : E.IsSymm)
    (e : Fin n → ℝ) (he : P *ᵥ e = 0) (hen : ‖WithLp.toLp 2 e‖ = 1)
    {ω : ℝ} (hω : chebyshev1.opNorm E ≤ ω) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((P * E * P) *ᵥ v)‖^2 ≤
      ω^2 * ‖WithLp.toLp 2 v‖^2 - ((P *ᵥ (E *ᵥ e)) ⬝ᵥ v)^2 := by
  let Y := P * E * P
  let x := P *ᵥ (E *ᵥ e)
  have hY : Y.IsSymm := by
    simp only [Y, Matrix.IsSymm, transpose_mul, hP.eq, hE.eq, Matrix.mul_assoc]
  have hc := (Matrix.le_iff.mp (matrix_compression_order P E hP hPid hE e he hen hω)).dotProduct_mulVec_nonneg v
  have hyn : ‖WithLp.toLp 2 (Y *ᵥ v)‖^2 = v ⬝ᵥ ((Y^2) *ᵥ v) := by
    rw [matrix_action_norm_sq, hY.eq, pow_two]
  obtain ⟨K, hK, hproj⟩ := matrix_projection_representation P hP hPid
  let : K.HasOrthogonalProjection := hK
  have hp := K.norm_starProjection_apply_le (WithLp.toLp 2 v)
  rw [← hproj, Matrix.toEuclideanCLM_toLp] at hp
  have hq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp
  rw [matrix_action_norm_sq, hP.eq, hPid] at hq
  -- The original matrix quadratic form is exactly its genuine Euclidean action energy.
  simp only [star_trivial, sub_mulVec, smul_mulVec, add_mulVec,
    krylov.Secant.outer_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at hc
  change 0 ≤ ω^2 * (v ⬝ᵥ (P *ᵥ v)) - (v ⬝ᵥ ((Y^2) *ᵥ v) + (x ⬝ᵥ v) * (v ⬝ᵥ x)) at hc
  have hpair : v ⬝ᵥ x = x ⬝ᵥ v := dotProduct_comm v x
  rw [hpair] at hc
  change ‖WithLp.toLp 2 (Y *ᵥ v)‖^2 ≤ _
  rw [hyn]
  nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg ω)]

end
end krylov.LinearAlgebra
