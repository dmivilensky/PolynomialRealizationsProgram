import krylov.XR.LocalFloorSource

/-!
Article: main_krylov, prop:floor, actual limiting-Hessian class bounds.
Use: derive the real matrix Loewner band from the original physical
coercivity and operator norm bounds. Matrix positivity is not an extra
analytic source assumption. Source: the true Euclidean matrix/inner-product
correspondence and Cauchy--Schwarz.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

theorem operator_bounds_spectral_band (base : Matrix (Fin n) (Fin n) ℝ)
    (hbase : base.PosDef) (a b : ℝ)
    (hlo : ∀ v : EuclideanSpace ℝ (Fin n), a*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hhi : ‖cgOperator base‖ ≤ b) :
    (base-a • 1).PosSemidef ∧ (b • 1-base).PosSemidef := by
  have hself (v : Fin n → ℝ) : v ⬝ᵥ v = ‖WithLp.toLp 2 v‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      (real_inner_self_eq_norm_sq (WithLp.toLp 2 v))
  have hm (v : Fin n → ℝ) : v ⬝ᵥ (base *ᵥ v) =
      inner ℝ (WithLp.toLp 2 v) (cgOperator base (WithLp.toLp 2 v)) := by
    simp only [cgOperator, Matrix.inner_toEuclideanCLM]
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hbase.isHermitian.sub (isHermitian_one.smul (show IsSelfAdjoint a from star_trivial a)))
    intro v
    simpa only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, hself, hm] using sub_nonneg.mpr (hlo (WithLp.toLp 2 v))
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((isHermitian_one.smul (show IsSelfAdjoint b from star_trivial b)).sub hbase.isHermitian)
    intro v
    have hh : inner ℝ (WithLp.toLp 2 v) (cgOperator base (WithLp.toLp 2 v)) ≤
        b*‖WithLp.toLp 2 v‖^2 := by
      calc
        _ ≤ ‖WithLp.toLp 2 v‖*‖cgOperator base (WithLp.toLp 2 v)‖ := real_inner_le_norm _ _
        _ ≤ ‖WithLp.toLp 2 v‖*(‖cgOperator base‖*‖WithLp.toLp 2 v‖) :=
          mul_le_mul_of_nonneg_left ((cgOperator base).le_opNorm _) (norm_nonneg _)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hhi (sq_nonneg ‖WithLp.toLp 2 v‖)]
    simpa only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, hself, hm] using sub_nonneg.mpr hh

end
end krylov.XR
