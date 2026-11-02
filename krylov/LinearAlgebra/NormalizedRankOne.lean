import krylov.LinearAlgebra.RankOneNorm
import krylov.Secant.Metric

/-!
Article: main_krylov, thm:window, normalization of the hidden information witness.
Use: the actual positive metric root gives a unit-norm rank-one canonical error.
Source: positive-definite quadratic forms and the proved exact spectral rank-one norm.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix krylov.Secant
open scoped Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Moving a rectangular operator across a real pairing transposes it.
Use: compute exact energies of the actual metric inverse and oldest dual vector.
Article: main_krylov, thm:window and apG:mss, dual-vector normalization.
Proof: associate the scalar pairing and use the standard transpose-action identity. -/
theorem transpose_pairing (M : Matrix (Fin n) (Fin p) ℝ) (u : Fin p → ℝ) (v : Fin n → ℝ) :
    (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- The actual inverse metric root realizes the inverse-base quadratic energy.
Use: prove the precise normalizing scalar in the information-radius witness.
Article: main_krylov, thm:window, ‖G^(−1/2)e₀‖²=(G⁻¹)₀₀.
Proof: move the symmetric inverse root across the Euclidean pairing and square it. -/
theorem inverseRoot_energy (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (e : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((metricRoot G)⁻¹ *ᵥ e)‖^2 = e ⬝ᵥ (G⁻¹ *ᵥ e) := by
  have hs : (metricRoot G)⁻¹ᵀ = (metricRoot G)⁻¹ := by
    rw [transpose_nonsing_inv, (metricRoot_isSymm G).eq]
  have hi : G⁻¹ = (metricRoot G)⁻¹ * (metricRoot G)⁻¹ := by
    conv_lhs => rw [← metricRoot_square G hG, Matrix.mul_inv_rev]
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial,
    transpose_pairing, hs, mulVec_mulVec, ← hi]

/-- The actual canonical normalization of a metric rank-one witness has spectral norm one.
Use: both hidden scenarios attain the full summed budget, not just a nonzero obstruction.
Article: main_krylov, thm:window, ‖ûûᵀ‖=1 for its printed metric normalization.
Proof: the canonical congruence transforms the generating vector by the actual
inverse root; its exact squared norm cancels the positive quadratic normalizer. -/
theorem normalized_relative_rankOne_norm (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (e : Fin n → ℝ) (he : e ≠ 0) :
    chebyshev1.opNorm (relativeOperator G
      ((e ⬝ᵥ (G⁻¹ *ᵥ e))⁻¹ • vecMulVec e e)) = 1 := by
  have hd : 0 < e ⬝ᵥ (G⁻¹ *ᵥ e) := by
    simpa only [star_trivial] using hG.inv.dotProduct_mulVec_pos he
  have hs : ((metricRoot G)⁻¹).IsSymm := by
    rw [Matrix.IsSymm, transpose_nonsing_inv, (metricRoot_isSymm G).eq]
  have hn := inverseRoot_energy G hG e
  simp only [relativeOperator, Matrix.mul_smul, Matrix.smul_mul,
    rankOne_inverse_congruence _ hs, chebyshev1.opNorm_smul, spectral_norm_rankOne,
    abs_of_nonneg (inv_nonneg.mpr hd.le), ← pow_two, hn, inv_mul_cancel₀ hd.ne']

/-- The printed unit direction is obtained by normalizing the actual inverse-root image.
Use: identify the precise rank-one canonical error, not just its spectral norm.
Article: main_krylov, thm:window, û=G⁻¹/²e₀/‖G⁻¹/²e₀‖. -/
def normalizedInverseRoot (G : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) : Fin n → ℝ :=
  ‖WithLp.toLp 2 ((metricRoot G)⁻¹ *ᵥ e)‖⁻¹ • ((metricRoot G)⁻¹ *ᵥ e)

/-- The actual normalized canonical rank-one form has the article's explicit unit generator.
Use: the two indistinguishable errors equal ±W ûûᵀ in the stated coordinates.
Article: main_krylov, thm:window, exact rank-one formula.
Proof: the inverse-root energy is the inverse-Gram normalizer; distribute the
two scalar normalizations in its outer product. -/
theorem normalized_relative_rankOne (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (e : Fin n → ℝ) :
    relativeOperator G ((e ⬝ᵥ (G⁻¹ *ᵥ e))⁻¹ • vecMulVec e e) =
      vecMulVec (normalizedInverseRoot G e) (normalizedInverseRoot G e) := by
  have hs : ((metricRoot G)⁻¹).IsSymm := by
    rw [Matrix.IsSymm, transpose_nonsing_inv, (metricRoot_isSymm G).eq]
  rw [relativeOperator_smul, relativeOperator, rankOne_inverse_congruence _ hs,
    normalizedInverseRoot, smul_vecMulVec, vecMulVec_smul, smul_smul,
    ← inverseRoot_energy G hG e]
  congr 1
  rw [pow_two, _root_.mul_inv_rev]

/-- The explicit canonical direction is a unit vector whenever its generating coordinate is nonzero.
Use: records the normalization and its nonzero denominator before using the witness.
Article: main_krylov, thm:window, ‖û‖=1.
Proof: positive inverse-Gram energy makes the actual inverse-root image nonzero. -/
theorem normalizedInverseRoot_unit (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (e : Fin n → ℝ) (he : e ≠ 0) : ‖WithLp.toLp 2 (normalizedInverseRoot G e)‖ = 1 := by
  -- Positive inverse energy rules out a zero normalization denominator.
  have hd : 0 < e ⬝ᵥ (G⁻¹ *ᵥ e) := by
    simpa only [star_trivial] using hG.inv.dotProduct_mulVec_pos he
  have hn : ‖WithLp.toLp 2 ((metricRoot G)⁻¹ *ᵥ e)‖ ≠ 0 := by
    intro hz
    have hh := inverseRoot_energy G hG e
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hh
    linarith
  simp only [normalizedInverseRoot, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]

end
end krylov.LinearAlgebra
