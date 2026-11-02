import krylov.Information.MetricComparison
import krylov.Information.TwinBudgets

/-!
Article: main_krylov, s4:cor-Q, sharp first-order physical metric comparison.
Use: obtain the exact 2W first-order dual-norm cost from the true 4W
common-twin base displacement, preserving the printed instance constant.
Source: exact rank-one relative spectral norm and physical Loewner budget
transfer; the elementary bound sqrt(1+v) <= 1+v/2 is applied by squaring.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Secant krylov.Reference krylov.LinearAlgebra
open scoped MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- True upper base displacement v changes every actual dual residual norm by at most 1+v/2.
Use: preserve the original source's first-order 2W metric cost for the common twin.
Article: main_krylov, s4:cor-Q, own-base residual normalization.
Proof: the real rank-one form of the residual transports by the proved true relative-budget upper-metric theorem. Its exact spectral norm gives the squared dual-norm comparison, and (1+v/2)^2 dominates 1+v. -/
theorem dual_norm_le_one_add_half (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) {v : ℝ} (hv : 0≤v) (hBA : B≤(1+v) • A)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖cgOperator (metricRoot A)⁻¹ g‖≤(1+v/2)*‖cgOperator (metricRoot B)⁻¹ g‖ := by
  -- Compare the same actual rank-one physical form in both genuine base metrics.
  let E := vecMulVec (WithLp.ofLp g) (WithLp.ofLp g)
  have hE : E.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [E,vecMulVec_apply]
    ring
  have he₀ : 0≤relativeBudget B E := norm_nonneg _
  have hb := relative_budget_upper_metric A B E hA hB hE (by linarith : 0≤1+v) he₀ hBA le_rfl
  have hsq : ‖cgOperator (metricRoot A)⁻¹ g‖^2≤(1+v)*‖cgOperator (metricRoot B)⁻¹ g‖^2 := by
    simpa only [E,relativeBudget_rankOne] using hb
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith : 0≤1+v/2) (norm_nonneg _))).mp
  have hscalar : 1+v≤(1+v/2)^2 := by nlinarith [sq_nonneg v]
  exact hsq.trans ((mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)).trans_eq (by ring))

end
end krylov.Information
