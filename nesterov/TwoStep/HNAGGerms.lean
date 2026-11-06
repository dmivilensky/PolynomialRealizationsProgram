import nesterov.TwoStep.AsymptoticsPhysical
import nesterov.Corner.Model

/-! The literal parameter germ obtained by eliminating the auxiliary HNAG++ state. -/
namespace nesterov.TwoStep.HNAG
noncomputable section
open Filter Set
open scoped Topology

def beta (ε : ℝ) : ℝ := 1/(1+Real.sqrt 2*ε)^2
def tau (ε : ℝ) : ℝ := 1/(2+Real.sqrt 2*ε)
def step (ε : ℝ) : ℝ := (2+Real.sqrt 2*ε)/(1+Real.sqrt 2*ε)^2

private theorem epsilon_zero : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
  continuous_id.continuousWithinAt.tendsto

theorem theta_tendsto :
    Tendsto (fun ε : ℝ=>(1-beta ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 (2*Real.sqrt 2)) := by
  have hh := ((tendsto_const_nhds (x:=2*Real.sqrt 2)).add
    (epsilon_zero.const_mul (Real.sqrt 2^2))).div
      (((tendsto_const_nhds (x:=(1:ℝ))).add (epsilon_zero.const_mul (Real.sqrt 2))).pow 2)
      (by norm_num : (1+Real.sqrt 2*0)^2≠0)
  simp only [mul_zero,add_zero,one_pow,div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  dsimp only [Pi.div_apply]
  unfold beta
  field_simp [hε.ne',show 1+Real.sqrt 2*ε≠0 by positivity]
  ring

theorem step_tendsto : Tendsto step (𝓝[>] (0:ℝ)) (𝓝 2) := by
  have hh := ((tendsto_const_nhds (x:=(2:ℝ))).add (epsilon_zero.const_mul (Real.sqrt 2))).div
      (((tendsto_const_nhds (x:=(1:ℝ))).add (epsilon_zero.const_mul (Real.sqrt 2))).pow 2)
      (by norm_num : (1+Real.sqrt 2*0)^2≠0)
  simp only [mul_zero,add_zero,one_pow,div_one] at hh
  convert hh using 1
  funext ε
  rfl

theorem tau_tendsto : Tendsto tau (𝓝[>] (0:ℝ)) (𝓝 (1/2)) := by
  have hh := (tendsto_const_nhds (x:=(1:ℝ))).div
      ((tendsto_const_nhds (x:=(2:ℝ))).add (epsilon_zero.const_mul (Real.sqrt 2)))
      (by norm_num : (2+Real.sqrt 2*0)≠0)
  simp only [mul_zero,add_zero] at hh
  convert hh using 1
  funext ε
  rfl

def family : Scaling ℝ (𝓝[>] (0:ℝ)) (2*Real.sqrt 2) 2 (1/2) :=
  fromRawLimits beta tau step (by positivity) (by norm_num) (by norm_num)
    theta_tendsto step_tendsto tau_tendsto

theorem parameters : ∀ᶠ ε in 𝓝[>] (0:ℝ),
    (family.tuning ε).beta=beta ε ∧ (family.tuning ε).tau=tau ε ∧
      (family.tuning ε).stepSize=step ε :=
  fromRawLimits_parameters _ _ _ (by positivity) (by norm_num) (by norm_num)
    theta_tendsto step_tendsto tau_tendsto

theorem corner_coordinates :
    Tendsto family.cornerA (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 2/4)) ∧
      Tendsto family.cornerB (𝓝[>] (0:ℝ)) (𝓝 (3*Real.sqrt 2)) := by
  constructor
  · have hh := (tendsto_const_nhds (x:=Real.sqrt 2)).div
        (((tendsto_const_nhds (x:=(2:ℝ))).add
          (epsilon_zero.const_mul (Real.sqrt 2))).const_mul 2)
        (by norm_num : 2*(2+Real.sqrt 2*0)≠0)
    simp only [mul_zero,add_zero] at hh
    norm_num at hh
    apply hh.congr'
    filter_upwards [parameters,self_mem_nhdsWithin] with ε hp hε
    change 0<ε at hε
    unfold Scaling.cornerA
    rw [hp.2.1]
    change Real.sqrt 2/(2*(2+Real.sqrt 2*ε))=(1/2-tau ε)/ε
    unfold tau
    field_simp [hε.ne',show 2+Real.sqrt 2*ε≠0 by positivity]
    ring
  · have hh := ((tendsto_const_nhds (x:=3*Real.sqrt 2)).add
        (epsilon_zero.const_mul (2*Real.sqrt 2^2))).div
        (((tendsto_const_nhds (x:=(1:ℝ))).add
          (epsilon_zero.const_mul (Real.sqrt 2))).pow 2)
        (by norm_num : (1+Real.sqrt 2*0)^2≠0)
    simp only [mul_zero,add_zero,one_pow,div_one] at hh
    apply hh.congr'
    filter_upwards [parameters,self_mem_nhdsWithin] with ε hp hε
    change 0<ε at hε
    unfold Scaling.cornerB
    rw [hp.2.2]
    change (3*Real.sqrt 2+(2*Real.sqrt 2^2)*ε)/(1+Real.sqrt 2*ε)^2=(2-step ε)/ε
    unfold step
    field_simp [hε.ne',show 1+Real.sqrt 2*ε≠0 by positivity]
    ring

end
end nesterov.TwoStep.HNAG
