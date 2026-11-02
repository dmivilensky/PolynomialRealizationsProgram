import krylov.Functions.HilbertPlaneMetricRealization
import krylov.Functions.HilbertPlaneHessianBounds

/-!
Article: main_krylov, prop:Fcycle(iii), genuine full-space cubic bounds.
Use: the orthogonal lift does not enlarge actual Hessian perturbations or
its global Lipschitz constant. These bounds discharge unrestricted true-error
conversion without any assumed output neighborhood.
Source: the real isometric embedding, contractive projection and binary Banach bound.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual full Hessian inherits the same true first-order drift.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_drift_norm (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : E) :
    ‖hilbertPlaneHessian e h p r t x-ContinuousLinearMap.id ℝ E‖≤
      ‖planeCubicHessian p r t (hilbertPlaneProject e h x)-ContinuousLinearMap.id ℝ Plane‖ := by
  rw [hilbertPlaneHessian_sub_id]
  exact hilbertPlaneLiftOperator_norm e h he hh heh _

/-- Actual full cubic Hessian differences are the exact constant third
variation on the actual displacement. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_sub (e h : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x y : E) :
    hilbertPlaneHessian e h p r t x-hilbertPlaneHessian e h p r t y=
      hilbertPlaneLiftOperator e h (canonicalVariation t.tensor (hilbertPlaneProject e h (x-y))) := by
  rw [←sub_sub_sub_cancel_right (hilbertPlaneHessian e h p r t x)
    (hilbertPlaneHessian e h p r t y) (ContinuousLinearMap.id ℝ E),
    hilbertPlaneHessian_sub_id,hilbertPlaneHessian_sub_id,←map_sub]
  congr 1
  rw [planeCubicHessian_terminal_identity,planeCubicHessian_terminal_identity]
  simp only [map_sub]
  abel

/-- The genuine full cubic Hessian is globally Lipschitz with exactly the
actual tensor amplitude. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneHessian_lipschitz (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (p r α : ℝ) (hα : 0≤α)
    {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) :
    LipschitzWith (Real.toNNReal α) (hilbertPlaneHessian e h p r (scaleBinaryCubic α t)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [Real.coe_toNNReal _ hα,hilbertPlaneHessian_sub]
  calc
    _ ≤ ‖canonicalVariation (scaleBinaryCubic α t).tensor (hilbertPlaneProject e h (x-y))‖ :=
      hilbertPlaneLiftOperator_norm e h he hh heh _
    _ = α*‖canonicalVariation t.tensor (hilbertPlaneProject e h (x-y))‖ := by
      rw [binary_canonicalVariation_scale,norm_smul,Real.norm_of_nonneg hα]
    _ ≤ α*‖hilbertPlaneProject e h (x-y)‖ :=
      mul_le_mul_of_nonneg_left (binary_canonicalVariation_norm ht _) hα
    _ ≤ α*‖x-y‖ := mul_le_mul_of_nonneg_left (hilbertPlaneProject_norm_le e h he hh heh _) hα

end
end krylov.Functions
