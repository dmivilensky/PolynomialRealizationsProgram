import krylov.Information.CompletionMidpoint

/-!
Article: main_krylov, thm:C2(c), actual primitive-budget midpoint estimates.
Use: the genuine observed-data consistency midpoint has its original
spectral-budget size and exact boundary-inclusive hidden-cross error bound,
including every zero budget, without any selector regularity hypothesis.
Source: true compact completion endpoints and the proved exact unit
midpoint estimates, scaled by the original nonnegative primitive budget.
-/

namespace krylov.Information
noncomputable section
open Matrix Set Finset krylov.Reference krylov.Secant krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
/-- The genuine data-only midpoint for an arbitrary nonnegative known spectral budget, with zero-budget output exactly zero.
Use: the actual informed algorithm uses the original primitive budget rather than an auxiliary unit-normalized hypothesis.
Article: main_krylov, thm:C2(c), budget-scaled consistency midpoint q̂. -/
def budgetCompletionMidpoint (ω : ℝ) (v e : EuclideanSpace ℝ (Fin n))
    (R : Matrix (Fin n) (Fin n) ℝ) : ℝ := ω*completionMidpoint v e (ω⁻¹ • R)

/-- The actual primitive-budget midpoint obeys both its true size bound and the exact hidden-cross error estimate, including zero budgets and singular endpoints.
Use: the genuine finite modified-solve tube can accept this data selector without a smoothness assumption.
Article: main_krylov, thm:C2(c), |q̂|≤ω and |q−q̂|≤ω(1−‖x‖²).
Proof: a zero budget forces the actual source matrix to vanish. Otherwise
normalize that true matrix by the positive budget and apply the proved
boundary-inclusive unit completion midpoint estimates. The actual quadratic
entry and midpoint both scale back by exactly the same original budget.
-/
theorem budgetCompletionMidpoint_bounds (ω : ℝ) (hω : 0≤ω)
    (v e : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖=1) (he : ‖e‖=1)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hRn : ‖R‖≤ω) :
    |budgetCompletionMidpoint ω v e R|≤ω ∧
      |completionQuadratic e R-budgetCompletionMidpoint ω v e R|≤
        ω*(1-‖cgOperator (ω⁻¹ • R) v-(inner ℝ v (cgOperator (ω⁻¹ • R) v)) • v‖^2) := by
  -- The degenerate original profile is handled without dividing by a vanishing budget.
  by_cases hw : ω=0
  · have hz : R=0 := norm_eq_zero.mp (le_antisymm (hRn.trans_eq hw) (norm_nonneg _))
    simp only [hw,hz,budgetCompletionMidpoint,zero_mul,completionQuadratic,cgOperator,map_zero,
      _root_.zero_apply,inner_zero_right,sub_zero,abs_zero,le_refl,and_self]
  · have hwpos : 0<ω := lt_of_le_of_ne hω (Ne.symm hw)
    have hunit : ‖ω⁻¹ • R‖≤1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hω)]
      exact (mul_le_mul_of_nonneg_left hRn (inv_nonneg.mpr hω)).trans_eq (inv_mul_cancel₀ hw)
    have hb := completionMidpoint_bounds v e hv he (ω⁻¹ • R) (hR.smul _) hunit
    have hentry : completionQuadratic e R=ω*completionQuadratic e (ω⁻¹ • R) := by
      simp only [completionQuadratic,cgOperator,map_smul,_root_.smul_apply,real_inner_smul_right]
      field_simp
    have hsize := mul_le_mul_of_nonneg_left hb.1 hω
    have herr := mul_le_mul_of_nonneg_left hb.2 hω
    refine ⟨?_,?_⟩
    · simpa only [budgetCompletionMidpoint,abs_mul,abs_of_nonneg hω,mul_one] using hsize
    · rw [hentry,budgetCompletionMidpoint,← mul_sub,abs_mul,abs_of_nonneg hω]
      exact herr

/-- Equal true observed restrictions give exactly equal original-budget midpoints, including zero budgets and impossible completion data.
Use: the informed final correction decision is genuinely data-only in the source's original budget scale.
Article: main_krylov, thm:C2(c), primitive-budget midpoint information invariance.
Proof: scalar normalization preserves every true observed action equality;
the exact unit-fibre midpoint invariance then preserves the scaled midpoint.
-/
theorem budgetCompletionMidpoint_congr (ω : ℝ) (v e : EuclideanSpace ℝ (Fin n))
    (R T : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ u : EuclideanSpace ℝ (Fin n), inner ℝ v u=0 → cgOperator R u=cgOperator T u) :
    budgetCompletionMidpoint ω v e R=budgetCompletionMidpoint ω v e T := by
  unfold budgetCompletionMidpoint
  congr 1
  apply completionMidpoint_congr
  intro u hu
  simp only [cgOperator,map_smul,_root_.smul_apply]
  exact congrArg (fun w => ω⁻¹ • w) (h u hu)

end
end krylov.Information
