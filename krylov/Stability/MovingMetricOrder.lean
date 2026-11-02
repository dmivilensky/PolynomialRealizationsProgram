import krylov.Stability.MetricRootRegularity
import krylov.Stability.C1VanishingProduct
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), true moving metric action order.
Use: transfer the actual quadratic physical output to its own actual A0
metric with a derived cubic cost in the full primitive parameter.
Source: genuine positive inverse-root regularity and the true first-order
metric variation acting on the actual quadratic physical vector.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Changing a genuine quadratic physical vector to its actual moving
positive reference metric costs cubic order, from primitive C-one data.
Use: native output formulas retain the source's own actual A0 inverse root.
Article: main_krylov, thm:local(a), genuine own-metric transfer.
Proof: the actual inverse positive root is C-one on the given primitive
positive domain, so its real reference difference is first order. Apply
the true operator norm product bound to the actual quadratic vector. -/
theorem moving_inverse_root_action_cubic
    (B : X → Matrix (Fin n) (Fin n) ℝ) (hB : ContDiffAt ℝ 1 B 0)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(B z).PosDef)
    (v : X → EuclideanSpace ℝ (Fin n)) (hv : v =O[𝓝 0] (fun z => ‖z‖^2)) :
    (fun z => cgOperator (metricRoot (B z))⁻¹ (v z)-cgOperator (metricRoot (B 0))⁻¹ (v z))
      =O[𝓝 0] (fun z => ‖z‖^3) := by
  let R := fun z => cgOperator (metricRoot (B z))⁻¹
  have hR : ContDiffAt ℝ 1 R 0 := matrixOperator_contDiffAt _ 0 (metricRoot_inverse_contDiffAt B 0 hB hpos)
  have hdiff : (fun z => R z-R 0) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using (hR.differentiableAt (by norm_num)).isBigO_sub.norm_right
  exact ((clm_apply_bigO (fun z => R z-R 0) v _ _ hdiff hv).congr_left
    (fun z => by rw [_root_.sub_apply])).congr_right (fun z => by ring)

end
end krylov.Stability
