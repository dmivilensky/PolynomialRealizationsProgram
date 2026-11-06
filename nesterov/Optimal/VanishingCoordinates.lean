import nesterov.Optimal.Model

/-! The unscaled corner perturbations vanish even when their scaled
coordinates are unbounded. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

theorem epsilon_cornerAlpha_tendsto :
    Tendsto (fun a=>F.epsilon a*F.cornerAlpha a) l (𝓝 0) := by
  have h : Tendsto (fun a=>(1/2-(F.tuning a).tau)*(F.tuning a).stepSize/2) l (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x:=(1/2:ℝ))).sub F.tau_tendsto).mul F.step_tendsto).div_const 2
  apply h.congr'
  filter_upwards [F.epsilon_pos] with a he
  unfold cornerAlpha
  field_simp

theorem epsilon_cornerDefect_tendsto :
    Tendsto (fun a=>F.epsilon a*F.cornerDefect a) l (𝓝 0) := by
  have h := ((F.epsilon_cornerAlpha_tendsto.const_mul 4).sub
    (F.epsilon_zero.const_mul 5)).max (tendsto_const_nhds (x:=(0:ℝ)))
  simp only [mul_zero,sub_self,max_self] at h
  apply h.congr'
  filter_upwards [F.epsilon_pos] with a he
  unfold cornerDefect
  rw [mul_max_of_nonneg _ _ he.le]
  ring_nf

theorem epsilon_stabilityMargin_tendsto :
    Tendsto (fun a=>F.epsilon a*F.stabilityMargin a) l (𝓝 0) := by
  convert F.corner_margin_numerator_tendsto using 1
  norm_num

theorem epsilon_cornerDenominator_tendsto :
    Tendsto (fun a=>F.epsilon a*(F.stabilityMargin a+5+F.cornerDefect a)) l (𝓝 0) := by
  have h := (F.epsilon_stabilityMargin_tendsto.add (F.epsilon_zero.const_mul 5)).add
    F.epsilon_cornerDefect_tendsto
  norm_num at h
  convert h using 1
  funext a
  ring

end
end nesterov.TwoStep.Scaling
