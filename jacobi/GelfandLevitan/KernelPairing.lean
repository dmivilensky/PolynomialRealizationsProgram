import jacobi.GelfandLevitan.FiniteKernelMaps
import jacobi.Reference.IntegralNorm

/-!
Article: jacobi, Proposition C.2.
The spatial bilinear integral is a bounded linear functional of the
continuous kernel. Consequently uniform kernel series, including both
parity subseries, can be paired with arbitrary original L2 inputs.
Use: kernelPairing is a genuine linear integral functional of the kernel.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- Every actual continuous-kernel bilinear integrand is integrable for arbitrary original L2 inputs.
Use: kernelPairing is a genuine linear integral functional of the kernel.
Article: jacobi, Proposition C.2.
Proof: both actual L2 inputs are L1 on the unchanged finite interval, and the continuous original kernel is bounded. -/
theorem continuousKernelPairing_integrable (v w : Space) (G : C(Interval×Interval,ℝ)) :
    Integrable (fun p:Interval×Interval => (v p.1*w p.2)*G p) (volume.prod volume) :=
  ((space_integrable v).mul_prod (space_integrable w)).mul_bdd
    G.continuous.aestronglyMeasurable (Eventually.of_forall G.norm_coe_le_norm)

/-- The actual continuous-kernel bilinear integral is bounded by the original input norms and the uniform kernel norm.
Use: proves boundedness of kernelPairing and transfers true uniform kernel convergence to the original L2 forms.
Article: jacobi, Proposition C.2.
Source: the earlier original L1/L2 inequality and the Bochner integral norm bound.
Proof: bound the kernel by its genuine supremum norm, factor the independent absolute input integrals, and use their original L1/L2 bounds. -/
theorem continuousKernelPairing_bound (v w : Space) (G : C(Interval×Interval,ℝ)) :
    ‖∫ p:Interval×Interval,(v p.1*w p.2)*G p ∂(volume.prod volume)‖≤
      (‖v‖*‖w‖)*‖G‖ := by
  -- The domain and its Lebesgue normalization are the original ones throughout.
  have hi := (space_integrable v).norm.mul_prod (space_integrable w).norm
  have hb := norm_integral_le_of_norm_le
    (f := fun p:Interval×Interval => (v p.1*w p.2)*G p) (hi.mul_const ‖G‖)
    (Eventually.of_forall (fun p:Interval×Interval => by
      rw [norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_left (G.norm_coe_le_norm p) (by positivity)))
  rw [integral_mul_const,integral_prod_mul (fun t:Interval => ‖v t‖) (fun s:Interval => ‖w s‖)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (space_L1_le_norm v) (space_L1_le_norm w)
      (integral_nonneg (fun _ => norm_nonneg _)) (norm_nonneg v)) (norm_nonneg G))

/-- The genuine bounded linear functional pairing a continuous kernel with two original physical L2 inputs.
Use: transports the original even and odd kernel series to their actual spectral coefficient forms in the two-bases argument.
Article: jacobi, Proposition C.2.
-/
def kernelPairing (v w : Space) : C(Interval×Interval,ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun G => ∫ p:Interval×Interval,(v p.1*w p.2)*G p ∂(volume.prod volume)
      map_add' := by
        intro G H
        simp only [ContinuousMap.add_apply,mul_add]
        exact integral_add (continuousKernelPairing_integrable v w G) (continuousKernelPairing_integrable v w H)
      map_smul' := by
        intro c G
        simp only [ContinuousMap.smul_apply,smul_eq_mul]
        simp_rw [mul_left_comm (v _*w _) c]
        exact integral_const_mul _ _ }
    (‖v‖*‖w‖) (continuousKernelPairing_bound v w)

end
end jacobi.GelfandLevitan
