import krylov.XR.QuadraticModel
import krylov.Nonlinear.GradientLocal

/-!
Article: main_krylov, lem:xr-local, genuine scalar-oracle perturbation.
Use: a true Hessian perturbation and matched initial function/gradient
give uniform closeness of the complete value/gradient oracle on a source
ball. Thus finite adaptive-query continuity applies before any native
query enclosure has been assumed.
Source: the actual derivative mean-value theorem on a convex ball.
-/

namespace krylov.XR
noncomputable section
open Set Metric krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Matched initial value and gradient and a true small Hessian error
control the actual full scalar oracle uniformly on a fixed source ball. -/
theorem scalar_oracle_error_on_ball (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (g₀ : E) (constant : ℝ) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (radius : ℝ) (hradius : 0 < radius) (epsilon : ℝ≥0)
    (hf₀ : f 0 = quadraticObjective Q g₀ constant 0) (hg₀ : G 0 = g₀)
    (hF : ∀ z ∈ ball 0 radius, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ ball 0 radius, HasFDerivAt G (H z) z)
    (hH : ∀ z ∈ ball 0 radius, ‖H z - Q‖ ≤ (epsilon : ℝ)) :
    ∀ z ∈ ball 0 radius,
      ‖(f z, G z) - (quadraticObjective Q g₀ constant z, quadraticGradient Q g₀ z)‖ ≤
        (epsilon : ℝ) * (radius + radius ^ 2 + 1) := by
  have hLip := gradient_error_lipschitzOn_of_hessian G H Q (ball 0 radius)
    (convex_ball 0 radius) hG hH
  have hgrad (z : E) (hz : z ∈ ball 0 radius) :
      ‖G z - quadraticGradient Q g₀ z‖ ≤ (epsilon : ℝ) * ‖z‖ := by
    have hh := hLip.norm_sub_le hz (mem_ball_self hradius)
    rw [map_zero, sub_zero, hg₀, sub_zero] at hh
    have he : (G z - Q z) - g₀ = G z - quadraticGradient Q g₀ z := by
      unfold quadraticGradient
      abel
    rwa [he] at hh
  let F : E → ℝ := fun z => f z - quadraticObjective Q g₀ constant z
  let D : E → E →L[ℝ] ℝ := fun z => innerSL ℝ (G z - quadraticGradient Q g₀ z)
  have hder (z : E) (hz : z ∈ ball 0 radius) : HasFDerivAt F (D z) z := by
    have hh := (hF z hz).sub (quadraticObjective_hasFDerivAt Q hQ g₀ constant z)
    convert hh using 1
    exact map_sub (innerSL ℝ) _ _
  have hnorm (z : E) (hz : z ∈ ball 0 radius) : ‖D z‖ ≤ (epsilon : ℝ) * radius := by
    dsimp only [D]
    rw [innerSL_apply_norm]
    exact (hgrad z hz).trans (mul_le_mul_of_nonneg_left (by
      exact (show ‖z‖ < radius by simpa only [mem_ball, dist_zero_right] using hz).le)
      epsilon.coe_nonneg)
  intro z hz
  have hvalue := (convex_ball (0 : E) radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hder z hz).hasFDerivWithinAt) hnorm (mem_ball_self hradius) hz
  have hzero : F 0 = 0 := by dsimp only [F]; rw [hf₀, sub_self]
  rw [hzero, sub_zero, sub_zero] at hvalue
  have hzr : ‖z‖ ≤ radius := (show ‖z‖ < radius by simpa only [mem_ball, dist_zero_right] using hz).le
  have hgradient := (hgrad z hz).trans (mul_le_mul_of_nonneg_left hzr epsilon.coe_nonneg)
  have hval : ‖F z‖ ≤ (epsilon : ℝ) * radius ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hzr (mul_nonneg epsilon.coe_nonneg hradius.le)
    nlinarith
  rw [Prod.mk_sub_mk, Prod.norm_def]
  apply max_le
  · change ‖F z‖ ≤ _
    exact hval.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg radius]) epsilon.coe_nonneg)
  · exact hgradient.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg radius]) epsilon.coe_nonneg)

end
end krylov.XR
