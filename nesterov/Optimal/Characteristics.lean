import nesterov.Optimal.NearCorner

/-! The endpoint characteristic clauses of the near-corner lemma, uniformly
for the test constant on compact sets. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

def nearSlowError (c : ℝ) (a : A) : ℝ :=
  (F.tuning a).stepSize-2-(F.tuning a).stepSize*(1+(F.tuning a).tau)*c*F.epsilon a+
    (θ-F.thetaAt a)*c

def nearFastError (c : ℝ) (a : A) : ℝ :=
  (F.tuning a).stepSize-2+F.epsilon a*(-(F.tuning a).stepSize*(1+(F.tuning a).tau)*c+
    F.epsilon a*(c^2-F.thetaAt a*c))

theorem near_slow_error_tendsto {c₀ : ℝ} {c : A→ℝ}
    (hc : Tendsto c l (𝓝 c₀)) : Tendsto (fun a=>F.nearSlowError (c a) a) l (𝓝 0) := by
  have h := ((F.step_tendsto.sub_const 2).sub ((((F.step_tendsto.mul
    ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto)).mul hc).mul F.epsilon_zero))).add
      (((tendsto_const_nhds (x:=θ)).sub F.theta_tendsto).mul hc)
  simpa only [nearSlowError,sub_self,mul_zero,sub_zero,zero_mul,add_zero,thetaAt] using h

theorem near_fast_error_tendsto {c₀ : ℝ} {c : A→ℝ}
    (hc : Tendsto c l (𝓝 c₀)) : Tendsto (fun a=>F.nearFastError (c a) a) l (𝓝 0) := by
  have h := (F.step_tendsto.sub_const 2).add (F.epsilon_zero.mul
    ((((F.step_tendsto.neg.mul ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto)).mul hc)).add
      (F.epsilon_zero.mul ((hc.pow 2).sub (F.theta_tendsto.mul hc)))))
  simpa only [nearFastError,sub_self,zero_mul,add_zero,thetaAt] using h

theorem near_slow_characteristic_exact (c : ℝ) : ∀ᶠ a in l,
    realCharacteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.epsilon a^2) (1-c*F.epsilon a)=
        F.epsilon a^2*(c^2-θ*c+2+F.nearSlowError c a) := by
  filter_upwards [F.beta_eq] with a hb
  rw [hb,realCharacteristic_slow]
  unfold Flow.delta nearSlowError
  ring

theorem near_fast_characteristic_exact (c : ℝ) : ∀ᶠ a in l,
    realCharacteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize 1
      (1-c*F.epsilon a)=2+F.nearFastError c a := by
  filter_upwards [F.beta_eq] with a hb
  rw [hb,scaled_chiL_exact]
  unfold nearFastError
  ring

theorem near_slow_error_uniform {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a c=>F.nearSlowError c a) (fun _=>0) l K := by
  apply Slow.uniform_on_compact_of_joint_limit continuous_const _ hK
  intro c
  exact (F.reindex Prod.fst tendsto_fst).near_slow_error_tendsto tendsto_snd

theorem near_fast_error_uniform {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun a c=>F.nearFastError c a) (fun _=>0) l K := by
  apply Slow.uniform_on_compact_of_joint_limit continuous_const _ hK
  intro c
  exact (F.reindex Prod.fst tendsto_fst).near_fast_error_tendsto tendsto_snd

theorem near_corner_negative_derivative :
    Tendsto (fun a=> -2-Quadratic.S (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize 1) l (𝓝 (-1)) := by
  have h := (tendsto_const_nhds (x:=(-2:ℝ))).sub (F.boundary_S_tendsto (by norm_num : (2:ℝ)*(1+2*(1/2))=4))
  convert h using 1
  norm_num

end
end nesterov.TwoStep.Scaling
