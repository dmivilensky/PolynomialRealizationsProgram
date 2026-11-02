import jacobi.Reference.JointContinuity

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
One genuine summable hypergeometric series bounds the actual reference
core uniformly on an energy disk and a smaller spatial disk. Cauchy's
estimate and the mean value theorem give a spatially linear remainder
and an energy Lipschitz bound with the same vanishing spatial factor.
Use: spatial analyticity of the original 2F1 function applies directly to the genuine energy-series core.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true square-root-free reference core equals its original community hypergeometric expression at every energy and argument.
Use: spatial analyticity of the original 2F1 function applies directly to the genuine energy-series core.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: replace every energy polynomial coefficient by its actual paired frequency coefficient at the true frequency root. -/
theorem energyCore_eq_waveCore (a : ℝ) (z x : ℂ) :
    energyCore a z x=waveCore a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) x := by
  unfold energyCore waveCore
  rw [ordinaryHypergeometric_eq_tsum]
  apply tsum_congr
  intro n
  rw [energyCoefficient_eq_frequency a (frequency_square _) n]
  rfl

/-- The actual original reference energy core is analytic in its spatial hypergeometric argument throughout the unit disk.
Use: Cauchy's derivative bound yields compact-uniform small-spatial-argument estimates for the true reference solution.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: identify the actual energy-series core with the genuine 2F1 function and use its proved disk analyticity. -/
theorem energyCore_spatial_analytic (a : ℝ) (z : ℂ) {x : ℂ} (hx : ‖x‖<1) :
    AnalyticAt ℂ (energyCore a z) x := by
  have he : energyCore a z=waveCore a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) :=
    funext (energyCore_eq_waveCore a z)
  rw [he]
  exact Hypergeometric.analytic hx

/-- The genuine original reference energy core has exactly central spatial value one at every complex energy.
Use: its actual constant term can be removed in the uniform endpoint and energy-difference estimates.
Article: jacobi, Proposition C.4.
Proof: the original community hypergeometric central value is one. -/
theorem energyCore_zero (a : ℝ) (z : ℂ) : energyCore a z 0=1 := by
  rw [energyCore_eq_waveCore]
  simp only [waveCore,ordinaryHypergeometric_zero]

/-- The actual original reference core has one uniform bound on a unit energy disk and the closed spatial disk of radius three quarters.
Use: supplies a genuine Cauchy bound for the small-spatial-argument and energy Lipschitz estimates, without a compactness premise.
Article: jacobi, Proposition C.4.
Proof: the actual energy coefficients are bounded by a fixed genuine
2F1 series at spatial radius three quarters. Its norm series is
summable. Bound every true term by that series and use the norm bound
for a genuinely convergent infinite sum. -/
theorem energyCore_uniform_bound (a : ℝ) (z0 : ℂ) :
    ∃ B : ℝ,0<B ∧ ∀ z∈Metric.ball z0 1,∀ x:ℂ,‖x‖≤3/4 → ‖energyCore a z x‖≤B := by
  -- The majorant is a genuine community hypergeometric series at a strict subradius, not an assumed uniform bound.
  obtain ⟨D,hD,hbound⟩ := energyCoefficient_bound a z0
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n‖*(3/4:ℝ)^n
  have hM : Summable M := by
    have hh := Hypergeometric.summable_norm (u := (D:ℂ)) (v := (D:ℂ))
      (c := ((gamma a:ℂ)+1/2)) (x := (3/4:ℂ)) (by norm_num)
    convert hh using 1
    funext n
    dsimp only [M]
    rw [norm_mul (ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n),norm_pow]
    norm_num
  refine ⟨(∑' n,M n)+1,by
    have hh : 0≤∑' n,M n := tsum_nonneg (fun n => by dsimp [M]; positivity)
    linarith,fun z hz x hx => ?_⟩
  have ht (n : ℕ) : ‖energyCoefficient a n z*x^n‖≤M n := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul (hbound z hz n) (pow_le_pow_left₀ (norm_nonneg _) hx n)
      (by positivity) (norm_nonneg _)
  have hs : Summable (fun n => ‖energyCoefficient a n z*x^n‖) :=
    hM.of_nonneg_of_le (fun _ => norm_nonneg _) ht
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum ht hM).trans (by linarith))

/-- The true original reference core has a uniformly bounded spatial derivative on a half-radius disk and a unit energy disk.
Use: integrates to a compact-uniform linear spatial remainder for the genuine reference solution.
Article: jacobi, Proposition C.4.
Proof: place a quarter-radius circle about the actual spatial point.
It stays inside the three-quarter disk, where the true uniform series
bound applies. Identify the community Cauchy derivative with the actual
derivative and apply its literal norm estimate. -/
theorem energyCore_spatial_deriv_bound (a : ℝ) (z0 : ℂ) :
    ∃ B : ℝ,0<B ∧ ∀ z∈Metric.ball z0 1,∀ x:ℂ,‖x‖≤1/2 →
      ‖deriv (energyCore a z) x‖≤B := by
  -- The derivative is the genuine ordinary complex derivative of the actual original energy core.
  obtain ⟨B,hB,hbound⟩ := energyCore_uniform_bound a z0
  refine ⟨4*B,by positivity,fun z hz x hx => ?_⟩
  have hclosed (w : ℂ) (hw : w∈Metric.closedBall x (1/4)) : ‖w‖≤3/4 := by
    have hh : ‖w-x‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
    have ht := norm_add_le (w-x) x
    rw [sub_add_cancel] at ht
    linarith
  have hd : DifferentiableOn ℂ (energyCore a z) (Metric.ball 0 1) := by
    intro w hw
    exact (energyCore_spatial_analytic a z (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv Metric.isOpen_ball hd (by norm_num : (0:ℝ)<1/4) (fun w hw => by
    simpa only [Metric.mem_ball,dist_zero_right] using lt_of_le_of_lt (hclosed w hw) (by norm_num : (3/4:ℝ)<1))]
  have hh := Complex.norm_cderiv_le (by norm_num : (0:ℝ)<1/4)
    (fun w hw => hbound z hz w (hclosed w (Metric.sphere_subset_closedBall hw)))
  convert hh using 1
  ring

/-- The actual reference core differs from one by a uniform spatially linear remainder on a unit energy disk.
Use: the true cosine coordinate vanishes quadratically, giving the compact-uniform selected endpoint expansion of f(t,z).
Article: jacobi, Proposition C.4.
Proof: the actual spatial derivative has a proved uniform bound on
the convex half-radius disk. Apply the genuine complex mean value
inequality from its actual central value one to the original argument. -/
theorem energyCore_remainder_bound (a : ℝ) (z0 : ℂ) :
    ∃ B : ℝ,0<B ∧ ∀ z∈Metric.ball z0 1,∀ x:ℂ,‖x‖≤1/2 →
      ‖energyCore a z x-1‖≤B*‖x‖ := by
  -- The estimate is simultaneous for every energy in the same original disk.
  obtain ⟨B,hB,hbound⟩ := energyCore_spatial_deriv_bound a z0
  refine ⟨B,hB,fun z hz x hx => ?_⟩
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℂ) (s := Metric.closedBall (0:ℂ) (1/2))
    (fun w hw => (energyCore_spatial_analytic a z (by
      have hh : ‖w‖≤1/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
      linarith)).differentiableAt)
    (fun w hw => hbound z hz w (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw))
    (convex_closedBall (0:ℂ) (1/2)) (by simp : (0:ℂ)∈Metric.closedBall 0 (1/2))
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
  simpa only [energyCore_zero,sub_zero] using hh


/-- The actual original core's energy derivative has a compact-uniform bound vanishing linearly in its spatial argument.
Use: gives the original reference energy Lipschitz estimate with the required extra endpoint order.
Article: jacobi, Proposition C.4.
Proof: apply the genuine energy Cauchy estimate to core-1 on a half-radius
circle. The circle remains in the original unit energy disk, where the
proved spatially linear remainder applies. Its constant term has zero
energy derivative, giving the true derivative of the original core. -/
theorem energyCore_energy_deriv_bound (a : ℝ) (z0 : ℂ) :
    ∃ B : ℝ,0<B ∧ ∀ x:ℂ,‖x‖≤1/2 → ∀ z∈Metric.closedBall z0 (1/4),
      ‖deriv (fun w => energyCore a w x) z‖≤B*‖x‖ := by
  -- The true energy analyticity includes the branch point, so Cauchy's estimate has no exceptional energy.
  obtain ⟨B,hB,hbound⟩ := energyCore_remainder_bound a z0
  refine ⟨2*B,by positivity,fun x hx z hz => ?_⟩
  have hx1 : ‖x‖<1 := by linarith
  have hd : DifferentiableOn ℂ (fun w => energyCore a w x-1) univ :=
    fun w _ => ((energyCore_analytic a hx1 w).sub analyticAt_const).differentiableAt.differentiableWithinAt
  have hcircle (w : ℂ) (hw : w∈Metric.sphere z (1/2)) : w∈Metric.ball z0 1 := by
    have hwz : ‖w-z‖=1/2 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hw
    have hzz0 : ‖z-z0‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have htriangle := norm_add_le (w-z) (z-z0)
    rw [sub_add_sub_cancel] at htriangle
    simp only [Metric.mem_ball,dist_eq_norm]
    linarith
  have hh := Complex.norm_cderiv_le (by norm_num : (0:ℝ)<1/2)
    (fun w hw => hbound w (hcircle w hw) x hx)
  rw [Complex.cderiv_eq_deriv isOpen_univ hd (by norm_num : (0:ℝ)<1/2) (subset_univ _),deriv_sub_const] at hh
  convert hh using 1
  ring

/-- The genuine original reference core has a compact-uniform energy Lipschitz bound with its actual vanishing spatial factor.
Use: after the true cosine substitution this is the source extra t^2 in f(t,z)-f(t,z').
Article: jacobi, Lemma C.1.
Proof: the actual energy derivative has the proved bound B*norm(x)
on the convex quarter-radius energy disk. Integrate it along the genuine
complex segment between the two original energies. -/
theorem energyCore_energy_lipschitz (a : ℝ) (z0 : ℂ) :
    ∃ B : ℝ,0<B ∧ ∀ x:ℂ,‖x‖≤1/2 → ∀ z∈Metric.closedBall z0 (1/4),
      ∀ w∈Metric.closedBall z0 (1/4),
        ‖energyCore a w x-energyCore a z x‖≤B*‖x‖*‖w-z‖ := by
  -- The statement controls both original energies simultaneously, rather than separately bounding their endpoint remainders.
  obtain ⟨B,hB,hbound⟩ := energyCore_energy_deriv_bound a z0
  refine ⟨B,hB,fun x hx z hz w hw => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℂ) (fun v _ => (energyCore_analytic a (by linarith : ‖x‖<1) v).differentiableAt)
    (fun v hv => hbound x hx v hv) (convex_closedBall z0 (1/4)) hz hw

end
end jacobi.Reference
