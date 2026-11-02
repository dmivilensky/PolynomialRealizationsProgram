import krylov.Functions.PlanarHessianFields

/-!
Article: main_krylov, prop:Fcycle(iii), actual minimizer-metric control.
Use: keep the original tensor diagonal budget while bounding the true affine
Hessian of the complete indistinguishable cubic family.
Source: proved Banach mixed bounds and the actual polynomial Hessian identity.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- Scaling the real coefficients scales the full actual trilinear tensor.
Article: main_krylov, prop:Fcycle(iii). -/
theorem scaleBinaryCubic_tensor_apply (a : ℝ) (t : krylov.Tensor.BinaryCubic) (u v w : Plane) :
    (scaleBinaryCubic a t).tensor.form u v w=a*t.tensor.form u v w := by
  simp only [tensor_apply,scaleBinaryCubic]
  ring

/-- The full genuine planar Hessian is symmetric in the physical Euclidean metric.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicHessian_symmetric (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    (planeCubicHessian p r t x).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ (planeCubicHessian p r t x u) v=inner ℝ u (planeCubicHessian p r t x v)
  simp [planeCubicHessian,planeValueHessianOperator,planeOfPair,
    PiLp.inner_apply,Fin.sum_univ_two,ContinuousLinearMap.smulRight_apply]
  ring

/-- The actual third-variation slice has its sharp diagonal-budget operator bound.
Article: main_krylov, prop:Fcycle(iii), genuine metric perturbation. -/
theorem binary_canonicalVariation_norm {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) (w : Plane) :
    ‖canonicalVariation t.tensor w‖≤‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  let z := canonicalVariation t.tensor w v
  have hh := tensor_bound ht w z v
  rw [←canonicalVariation_pair,show canonicalVariation t.tensor w v=z from rfl,
    real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hh
  have he : ‖w‖*‖z‖*‖v‖=(‖w‖*‖v‖)*‖z‖ := by ring
  rw [he] at hh
  change ‖z‖≤‖w‖*‖v‖
  by_cases hz : z=0
  · rw [hz,norm_zero]
    positivity
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz
  nlinarith only [hh,hn]

/-- Both tensor budget and true terminal Hessian perturbation scale exactly.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeTerminalOperator_scale (a r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    planeTerminalOperator r (scaleBinaryCubic a t)=a • planeTerminalOperator r t := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;> simp [planeTerminalOperator,planeOfPair,scaleBinaryCubic,
    ContinuousLinearMap.smulRight_apply] <;> ring

/-- The actual third-variation slice scales by the true tensor coefficient.
Article: main_krylov, prop:Fcycle(iii). -/
theorem binary_canonicalVariation_scale (a : ℝ) (t : krylov.Tensor.BinaryCubic) (w : Plane) :
    canonicalVariation (scaleBinaryCubic a t).tensor w=a • canonicalVariation t.tensor w := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro z
  rw [canonicalVariation_pair]
  change _=inner ℝ z (a • canonicalVariation t.tensor w v)
  rw [inner_smul_right,canonicalVariation_pair,scaleBinaryCubic_tensor_apply]

/-- The true scaled-family Hessian is controlled from the genuine diagonal
budget, including the original varying quadratic perturbation.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicHessian_scaled_lower (p r a : ℝ) (hp : 0≤p) (ha : 0≤a)
    {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) (x v : Plane) :
    (1-a*p*‖planeTerminalOperator r t‖-a*‖x-planeOfPair (p,r*p)‖)*‖v‖^2≤
      inner ℝ v (planeCubicHessian p r (scaleBinaryCubic a t) x v) := by
  rw [planeCubicHessian_terminal_identity,planeTerminalOperator_scale,binary_canonicalVariation_scale]
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,inner_add_right,inner_smul_right,
    real_inner_self_eq_norm_sq,canonicalVariation_pair]
  have hT := (abs_le.mp (tensor_bound ht (x-planeOfPair (p,r*p)) v v)).1
  have hL : -‖planeTerminalOperator r t‖*‖v‖^2≤ inner ℝ v (planeTerminalOperator r t v) := by
    have hh := (abs_real_inner_le_norm v (planeTerminalOperator r t v)).trans
      (mul_le_mul_of_nonneg_left ((planeTerminalOperator r t).le_opNorm v) (norm_nonneg v))
    have hl := (abs_le.mp hh).1
    nlinarith only [hl]
  have h1 := mul_le_mul_of_nonneg_left hL (mul_nonneg ha hp)
  have h2 := mul_le_mul_of_nonneg_left hT ha
  nlinarith only [h1,h2]

end
end krylov.Functions
