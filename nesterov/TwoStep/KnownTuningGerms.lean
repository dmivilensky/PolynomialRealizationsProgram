import nesterov.TwoStep.AsymptoticsPhysical

/-! Explicit accelerated-scaling germs for the known tunings of Corollary B. -/
namespace nesterov.TwoStep.KnownTunings
noncomputable section
open Filter Set
open scoped Topology

def standardBeta (ε : ℝ) : ℝ := (1-ε)/(1+ε)
def quadraticOptimalBeta (ε : ℝ) : ℝ := (Real.sqrt (3+ε^2)-2*ε)/(Real.sqrt (3+ε^2)+2*ε)
def quadraticOptimalStep (ε : ℝ) : ℝ := 4/(3+ε^2)
def classOptimalBeta (ε : ℝ) : ℝ := 1-Real.sqrt 6*ε
def overrelaxedStep (ε : ℝ) : ℝ := (1+ε)⁻¹^2

private theorem epsilon_zero : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
  continuous_id.continuousWithinAt.tendsto

theorem standard_theta_tendsto :
    Tendsto (fun ε : ℝ=>(1-standardBeta ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 2) := by
  have ht : Tendsto (fun ε : ℝ=>2/(1+ε)) (𝓝[>] (0:ℝ)) (𝓝 2) := by
    have hh := (tendsto_const_nhds (x:=(2:ℝ))).div
      ((tendsto_const_nhds (x:=(1:ℝ))).add epsilon_zero) (by norm_num : (1+0:ℝ)≠0)
    simp only [add_zero,div_one] at hh
    convert hh using 1
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  unfold standardBeta
  field_simp [hε.ne',show 1+ε≠0 by linarith]
  ring

theorem standard_beta_tendsto : Tendsto standardBeta (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).sub epsilon_zero).div
      ((tendsto_const_nhds (x:=(1:ℝ))).add epsilon_zero) (by norm_num : (1+0:ℝ)≠0)
  simp only [sub_zero,add_zero,div_one] at hh
  convert hh using 1
  funext ε
  rfl

def standard : Scaling ℝ (𝓝[>] (0:ℝ)) 2 1 1 :=
  fromRawLimits standardBeta standardBeta (fun _=>1) (by norm_num) (by norm_num) (by norm_num)
    standard_theta_tendsto tendsto_const_nhds standard_beta_tendsto

theorem quadraticOptimal_theta_tendsto :
    Tendsto (fun ε : ℝ=>(1-quadraticOptimalBeta ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 (4/Real.sqrt 3)) := by
  have hs : Tendsto (fun ε : ℝ=>Real.sqrt (3+ε^2)) (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 3)) := by
    simpa only [zero_pow (by omega : 2≠0),add_zero] using
      ((tendsto_const_nhds (x:=(3:ℝ))).add (epsilon_zero.pow 2)).sqrt
  have ht := (tendsto_const_nhds (x:=(4:ℝ))).div (hs.add (epsilon_zero.const_mul 2))
    (show Real.sqrt 3+2*0≠0 by positivity)
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  dsimp only [Pi.div_apply]
  unfold quadraticOptimalBeta
  field_simp [hε.ne',show Real.sqrt (3+ε^2)+2*ε≠0 by positivity]
  ring

theorem quadraticOptimal_beta_tendsto :
    Tendsto quadraticOptimalBeta (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hs : Tendsto (fun ε : ℝ=>Real.sqrt (3+ε^2)) (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 3)) := by
    simpa only [zero_pow (by omega : 2≠0),add_zero] using
      ((tendsto_const_nhds (x:=(3:ℝ))).add (epsilon_zero.pow 2)).sqrt
  have ht := (hs.sub (epsilon_zero.const_mul 2)).div (hs.add (epsilon_zero.const_mul 2))
    (show Real.sqrt 3+2*0≠0 by positivity)
  simp only [mul_zero,sub_zero,add_zero,div_self (show Real.sqrt 3≠0 by positivity)] at ht
  convert ht using 1
  funext ε
  rfl

theorem quadraticOptimal_step_tendsto :
    Tendsto quadraticOptimalStep (𝓝[>] (0:ℝ)) (𝓝 (4/3)) := by
  have ht := (tendsto_const_nhds (x:=(4:ℝ))).div
      ((tendsto_const_nhds (x:=(3:ℝ))).add (epsilon_zero.pow 2)) (by norm_num : (3+0^2:ℝ)≠0)
  simp only [zero_pow (by omega : 2≠0),add_zero] at ht
  convert ht using 1
  funext ε
  rfl

def quadraticOptimal : Scaling ℝ (𝓝[>] (0:ℝ)) (4/Real.sqrt 3) (4/3) 1 :=
  fromRawLimits quadraticOptimalBeta quadraticOptimalBeta quadraticOptimalStep
    (by positivity) (by norm_num) (by norm_num) quadraticOptimal_theta_tendsto
    quadraticOptimal_step_tendsto quadraticOptimal_beta_tendsto

theorem classOptimal_theta_tendsto :
    Tendsto (fun ε : ℝ=>(1-classOptimalBeta ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 6)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  unfold classOptimalBeta
  field_simp [hε.ne']
  ring

theorem classOptimal_beta_tendsto : Tendsto classOptimalBeta (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (epsilon_zero.const_mul (Real.sqrt 6))
  simp only [mul_zero,sub_zero] at hh
  convert hh using 1
  funext ε
  rfl

def classOptimal : Scaling ℝ (𝓝[>] (0:ℝ)) (Real.sqrt 6) (4/3) 1 :=
  fromRawLimits classOptimalBeta classOptimalBeta (fun _=>4/3)
    (by positivity) (by norm_num) (by norm_num) classOptimal_theta_tendsto
    tendsto_const_nhds classOptimal_beta_tendsto

theorem overrelaxed_step_tendsto : Tendsto overrelaxedStep (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hh := (((tendsto_const_nhds (x:=(1:ℝ))).add epsilon_zero).inv₀
    (by norm_num : (1+0:ℝ)≠0)).pow 2
  simp only [add_zero,inv_one,one_pow] at hh
  convert hh using 1
  funext ε
  rfl

theorem overrelaxed_theta_tendsto :
    Tendsto (fun ε : ℝ=>(1-overrelaxedStep ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 2) := by
  have hh := ((tendsto_const_nhds (x:=(2:ℝ))).add epsilon_zero).div
    (((tendsto_const_nhds (x:=(1:ℝ))).add epsilon_zero).pow 2) (by norm_num : (1+0:ℝ)^2≠0)
  simp only [add_zero,one_pow,div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  dsimp only [Pi.div_apply]
  unfold overrelaxedStep
  field_simp [hε.ne',show 1+ε≠0 by linarith]
  ring

def overrelaxed : Scaling ℝ (𝓝[>] (0:ℝ)) 2 1 1 :=
  fromRawLimits overrelaxedStep (fun _=>1) overrelaxedStep (by norm_num) (by norm_num) (by norm_num)
    overrelaxed_theta_tendsto overrelaxed_step_tendsto tendsto_const_nhds

theorem standard_parameters : ∀ᶠ ε in 𝓝[>] (0:ℝ),
    (standard.tuning ε).beta=standardBeta ε ∧ (standard.tuning ε).tau=standardBeta ε ∧
      (standard.tuning ε).stepSize=1 :=
  fromRawLimits_parameters _ _ _ (by norm_num) (by norm_num) (by norm_num)
    standard_theta_tendsto tendsto_const_nhds standard_beta_tendsto

theorem quadraticOptimal_parameters : ∀ᶠ ε in 𝓝[>] (0:ℝ),
    (quadraticOptimal.tuning ε).beta=quadraticOptimalBeta ε ∧
      (quadraticOptimal.tuning ε).tau=quadraticOptimalBeta ε ∧
      (quadraticOptimal.tuning ε).stepSize=quadraticOptimalStep ε :=
  fromRawLimits_parameters _ _ _ (by positivity) (by norm_num) (by norm_num)
    quadraticOptimal_theta_tendsto quadraticOptimal_step_tendsto quadraticOptimal_beta_tendsto

theorem classOptimal_parameters : ∀ᶠ ε in 𝓝[>] (0:ℝ),
    (classOptimal.tuning ε).beta=classOptimalBeta ε ∧ (classOptimal.tuning ε).tau=classOptimalBeta ε ∧
      (classOptimal.tuning ε).stepSize=4/3 :=
  fromRawLimits_parameters _ _ _ (by positivity) (by norm_num) (by norm_num)
    classOptimal_theta_tendsto tendsto_const_nhds classOptimal_beta_tendsto

theorem overrelaxed_parameters : ∀ᶠ ε in 𝓝[>] (0:ℝ),
    (overrelaxed.tuning ε).beta=overrelaxedStep ε ∧ (overrelaxed.tuning ε).tau=1 ∧
      (overrelaxed.tuning ε).stepSize=overrelaxedStep ε :=
  fromRawLimits_parameters _ _ _ (by norm_num) (by norm_num) (by norm_num)
    overrelaxed_theta_tendsto overrelaxed_step_tendsto tendsto_const_nhds

end
end nesterov.TwoStep.KnownTunings
