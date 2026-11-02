import jacobi.GelfandLevitan.FullWaveProfiles
import jacobi.GelfandLevitan.TargetGreenOperator
import jacobi.GelfandLevitan.ProfileSeries

/-!
Article: jacobi, Theorem 2.1.
The genuine continuous full target waves define a uniformly convergent
Green kernel series on the entire closed physical square. Its pointwise
diagonal is exactly half the original persymmetric profile, so the
original c_star is four times its squared diagonal integral. The same
kernel's actual full L2 inverse action is proved in TargetGreenAction.
Use: targetGreenKernelMap sums precisely v_k(t)*v_k(s)/sigma_k with the unchanged original transformed waves and target eigenvalues.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- Each genuine original continuous Green series summand on the full physical square.
Use: targetGreenKernelMap sums precisely v_k(t)*v_k(s)/sigma_k with the unchanged original transformed waves and target eigenvalues.
Article: jacobi, Theorem 2.1.
-/
def targetGreenKernelTerm (a : ℝ) (ha : -1<a) (k : ℕ) : C(Interval×Interval,ℝ) :=
  ⟨fun p => (jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k p.1*fullWaveMap a ha k p.2,
    (continuous_const.mul ((fullWaveMap a ha k).continuous.comp continuous_fst)).mul
      ((fullWaveMap a ha k).continuous.comp continuous_snd)⟩

/-- The actual full Green kernel summands have genuinely summable uniform norms.
Use: targetGreenKernelMap is a true uniform continuous-kernel sum, justifying the original full-square convergence and all subsequent bounded integral pairings.
Article: jacobi, Theorem 2.1.
Proof: the proved actual full waves have one all-index uniform bound D. Every genuine kernel term is bounded by D^2/sigma_k, and the independently proved original inverse sigma sequence is absolutely summable. -/
theorem targetGreenKernelTerm_norm_summable (a : ℝ) (ha : -1<a) :
    Summable (fun k => ‖targetGreenKernelTerm a ha k‖) := by
  -- Both the spectral summability and the uniform wave bound concern the unchanged original data, including the genuine finite prefix.
  obtain ⟨D,hD,hbound⟩ := fullWaveMap_uniform_bound a ha
  have hM := (target_inverse_spectrum_summable a ha).mul_right (D^2)
  apply hM.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  apply ((targetGreenKernelTerm a ha k).norm_le (by positivity)).mpr
  intro p
  change ‖(jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k p.1*fullWaveMap a ha k p.2‖≤_
  rw [norm_mul,norm_mul,Real.norm_eq_abs]
  have ht := ((fullWaveMap a ha k).norm_coe_le_norm p.1).trans (hbound k)
  have hs := ((fullWaveMap a ha k).norm_coe_le_norm p.2).trans (hbound k)
  exact (mul_le_mul (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hs (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The original Green kernel as a genuine continuous map on the full closed physical square.
Use: targetGreenKernel is the printed pointwise kernel, and TargetGreenAction identifies its actual integral action with H_alpha^(-1).
Article: jacobi, Theorem 2.1.
-/
def targetGreenKernelMap (a : ℝ) (ha : -1<a) : C(Interval×Interval,ℝ) :=
  ∑' k,targetGreenKernelTerm a ha k

/-- The actual original pointwise full Green kernel, retaining its genuine continuous-kernel representative.
Use: targetGreen_diagonal and targetGreen_integral_action give the exact original diagonal and full inverse operator identities.
Article: jacobi, Theorem 2.1.
-/
def targetGreenKernel (a : ℝ) (ha : -1<a) (t s : Interval) : ℝ :=
  targetGreenKernelMap a ha (t,s)

/-- The original full Green kernel has exactly its printed spectral series at every physical point, including both endpoints and midpoint lines.
Use: targetGreen_diagonal identifies the genuine original spectral profile with the actual Green diagonal.
Article: jacobi, Theorem 2.1.
Proof: the genuine point-evaluation functional commutes with the independently proved norm-summable continuous-kernel series. -/
theorem targetGreenKernel_apply (a : ℝ) (ha : -1<a) (t s : Interval) :
    targetGreenKernel a ha t s=∑' k,(jacobi.Bessel.sigma a ha k)⁻¹*
      fullWaveMap a ha k t*fullWaveMap a ha k s :=
  (ContinuousMap.evalCLM ℝ (t,s)).map_tsum (targetGreenKernelTerm_norm_summable a ha).of_norm

/-- The original natural Green kernel partial sums converge uniformly on the entire closed physical square.
Use: the actual continuous kernel in the inverse statement is the genuine original uniformly convergent series, with no spatial region omitted.
Article: jacobi, Theorem 2.1.
Proof: the independently proved norm-summable original kernel series has its actual continuous-map norm limit, which is precisely uniform convergence on the compact original square. -/
theorem targetGreenKernel_uniform_limit (a : ℝ) (ha : -1<a) :
    TendstoUniformly (fun N (p:Interval×Interval) =>
      ∑ k∈Finset.range N,(jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k p.1*fullWaveMap a ha k p.2)
      (fun p => targetGreenKernel a ha p.1 p.2) atTop := by
  have h := (targetGreenKernelTerm_norm_summable a ha).of_norm.hasSum.tendsto_sum_nat
  simpa only [ContinuousMap.sum_apply,targetGreenKernelTerm,ContinuousMap.coe_mk,
    targetGreenKernel,targetGreenKernelMap] using ContinuousMap.tendsto_iff_tendstoUniformly.mp h

/-- The actual original Green kernel is symmetric in its two genuine physical arguments.
Use: the full target inverse integral action and diagonal are compatible with the genuine self-adjoint spectral realization.
Article: jacobi, Theorem 2.1.
Proof: commute the two true real wave factors in every summand of the original genuinely convergent series. -/
theorem targetGreenKernel_symmetric (a : ℝ) (ha : -1<a) (t s : Interval) :
    targetGreenKernel a ha t s=targetGreenKernel a ha s t := by
  rw [targetGreenKernel_apply,targetGreenKernel_apply]
  apply tsum_congr
  intro k
  ring

/-- Twice the actual full Green diagonal equals the original constructed persymmetric profile at every physical point.
Use: persymmetricConstant_green_diagonal proves the original exact c_star identity for the same genuine Green inverse kernel.
Article: jacobi, Theorem 2.1.
Proof: each true full wave square is exactly Phi_k, and the original Lambda_k is 2/sigma_k. Multiply the genuine Green series by two and identify every unchanged original profile summand. -/
theorem targetGreen_diagonal (a : ℝ) (ha : -1<a) (t : Interval) :
    2*targetGreenKernel a ha t t=persymmetricProfile a ha t := by
  rw [targetGreenKernel_apply,persymmetricProfile_apply,← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [show (jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k t*fullWaveMap a ha k t=
    (jacobi.Bessel.sigma a ha k)⁻¹*(fullWaveMap a ha k t)^2 by ring,fullWaveMap_sq]
  unfold jacobi.Bessel.edgeValue
  ring

/-- The original persymmetric constant is exactly four times the squared actual Green-diagonal integral.
Use: completes the original diagonal-energy identification in the full target Green realization and its special-order applications.
Article: jacobi, Theorem 2.1.
Proof: the original c_star is the genuine squared-profile integral; substitute the independently proved exact original profile equals twice the actual Green diagonal, square, and take the fixed scalar outside the true Lebesgue integral. -/
theorem persymmetricConstant_green_diagonal (a : ℝ) (ha : -1<a) :
    persymmetricConstant a ha=4*∫ t:Interval,(targetGreenKernel a ha t t)^2 := by
  rw [persymmetricConstant,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by dsimp only; rw [← targetGreen_diagonal]; ring)

end
end jacobi.GelfandLevitan
