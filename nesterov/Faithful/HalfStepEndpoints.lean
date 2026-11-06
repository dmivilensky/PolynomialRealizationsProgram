import nesterov.Faithful.HalfStep

/-! The source defines the limit phase only where the endpoint product is
nonzero. TMM's endpoint at pi is excluded by that very definition. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial

theorem tmm_product_at_pi :
    limitProduct (momentumQuery (1/2)) (C (-1/2)) Real.pi=0 := by
  have hc : circle Real.pi=(-1:ℂ) := Complex.exp_pi_mul_I
  norm_num [limitProduct,momentumQuery,evalComplex,hc]

theorem limitProduct_at_zero (u q : Polynomial ℝ) : limitProduct u q 0=0 := by
  simp [limitProduct,circle]

end
end nesterov.Faithful
