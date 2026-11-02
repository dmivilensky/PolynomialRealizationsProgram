import krylov.Information.PlanarAdmissibility
import krylov.LinearAlgebra.NormalizedRankOne

/-!
Article: main_krylov, thm:C, actual own-base dual norm comparison.
Use: transfer the fixed-reference lower residual to the genuine metric of
each explicitly constructed admissible base without assuming a norm estimate.
Source: exact rank-one spectral norms and the proved Loewner budget transfer.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Secant krylov.Reference krylov.LinearAlgebra
open scoped MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A real dual vector's squared actual inverse-root norm is the relative spectral budget of its genuine rank-one form.
Use: reduce the source residual metric change to the existing physical budget comparison.
Article: main_krylov, thm:C, ‖g‖_(A⁻¹)²=‖A^(−1/2)ggᵀA^(−1/2)‖.
Proof: the true inverse-root congruence transforms the actual outer product
into the outer product of the actual inverse-root vector. Its exact spectral
norm is the square of that genuine Euclidean vector norm.
-/
theorem relativeBudget_rankOne (A : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) :
    relativeBudget A (vecMulVec (WithLp.ofLp g) (WithLp.ofLp g))=
      ‖cgOperator (metricRoot A)⁻¹ g‖^2 := by
  have hs : ((metricRoot A)⁻¹).IsSymm := by
    rw [Matrix.IsSymm,transpose_nonsing_inv,(metricRoot_isSymm A).eq]
  rw [relativeBudget,relativeOperator,rankOne_inverse_congruence _ hs,spectral_norm_rankOne]
  change ‖cgOperator (metricRoot A)⁻¹ g‖*‖cgOperator (metricRoot A)⁻¹ g‖=_
  ring

/-- Actual Loewner base domination controls every genuine dual residual norm with an explicit uniform factor.
Use: compare each constructed scenario's own metric with the original physical reference metric.
Article: main_krylov, thm:C, ‖g‖_(A⁻¹)≤(1+W)‖g‖_(B⁻¹) when B≼(1+W)A.
Proof: apply the proved exact budget-transfer theorem to the actual rank-one
form ggᵀ after rescaling the base domination. Exact rank-one normalization
turns the resulting budget inequality into the squared dual-norm bound;
c≥1 permits the stated linear factor without introducing a square root.
-/
theorem dual_norm_le_of_base_upper (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) {c : ℝ} (hc : 1≤c) (hBA : B≤c • A)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖cgOperator (metricRoot A)⁻¹ g‖≤c*‖cgOperator (metricRoot B)⁻¹ g‖ := by
  -- Use the same real rank-one form in both actual physical metrics.
  let E := vecMulVec (WithLp.ofLp g) (WithLp.ofLp g)
  have hE : E.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [E,vecMulVec_apply]
    ring
  have hcpos : 0<c := by linarith
  have hscale : c⁻¹ • B≤A := by
    have h := smul_le_smul_of_nonneg_left hBA (inv_nonneg.mpr hcpos.le)
    simpa only [smul_smul,inv_mul_cancel₀ hcpos.ne',one_smul] using h
  have hb : relativeBudget B E≤c⁻¹*(c*relativeBudget B E) := by
    rw [← mul_assoc,inv_mul_cancel₀ hcpos.ne',one_mul]
  have he₀ : 0≤relativeBudget B E := norm_nonneg _
  have hbudget := relative_budget_change B A E hB hA hE (inv_nonneg.mpr hcpos.le)
    (mul_nonneg hcpos.le he₀) hscale hb
  have hsq : ‖cgOperator (metricRoot A)⁻¹ g‖^2≤c*‖cgOperator (metricRoot B)⁻¹ g‖^2 := by
    simpa only [E,relativeBudget_rankOne] using hbudget
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcpos.le (norm_nonneg _))).mp
  calc
    _ ≤ c*‖cgOperator (metricRoot B)⁻¹ g‖^2 := hsq
    _ ≤ c^2*‖cgOperator (metricRoot B)⁻¹ g‖^2 :=
      mul_le_mul_of_nonneg_right (by nlinarith : c≤c^2) (sq_nonneg _)
    _ = _ := by ring

end
end krylov.Information
