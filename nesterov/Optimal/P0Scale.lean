import nesterov.Layer.SymbolLimits

/-! The constant term is negligible at every variable band scale satisfying
ε/σ²→0. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem P0_at_scale_tendsto (c : ℝ) {σ : A→ℝ}
    (hσ : Tendsto σ l (𝓝[>] (0:ℝ)))
    (hsmall : Tendsto (fun a=>F.epsilon a/σ a^2) l (𝓝 0)) :
    Tendsto (fun a=>scaledP0 (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/(F.epsilon a*σ a)) l (𝓝 0) := by
  have hσ0 := hσ.mono_right nhdsWithin_le_nhds
  have ht := (((hsmall.mul (F.epsilon_zero.mul hσ0)).const_mul c).mul
    (F.slow_test_tendsto c)).mul (F.characteristic_at_radius_tendsto c 1)
  simp only [zero_mul,mul_zero] at ht
  apply ht.congr'
  filter_upwards [F.epsilon_pos,F.beta_eq,hσ.eventually self_mem_nhdsWithin] with a he hb hs
  rw [scaledP0_exact,realCharacteristic_slow,←hb]
  field_simp

end
end nesterov.TwoStep.Scaling
