import polyak.Spiral.Feasibility
import polyak.Spiral.Threshold
import polyak.Threshold.Parameters

/-!
Article: the limiting three-cycle in Proposition spiral and Theorem threshold.
Use: identify the exact critical atom and prove genuine period three of its wave.
Proof: the unit complex number with real part -1/2 is a nontrivial cubic root of unity.
-/

noncomputable section

namespace polyak.Spiral

open Spectral Waves

/-- Article: the critical cosine is exactly -1/2. -/
@[simp] theorem cosine_zero : cosine 0 = -(1/2 : ℝ) := by norm_num [cosine,G]

/-- Article: the critical twist is exactly 1/2. -/
@[simp] theorem twist_zero : twist 0 = (1/2 : ℝ) := by norm_num [twist,G]

/-- Article: the critical minimizer slack is exactly 1/2. -/
@[simp] theorem gap_zero : gap 0 = (1/2 : ℝ) := by norm_num [gap,G]

/-- Article: the critical common value constant is zero. -/
@[simp] theorem valueConstant_zero : valueConstant 0 = 0 := by simp [valueConstant]

/-- Article: the exact angle of the critical wave is 2π/3. -/
theorem angle_zero : Real.arccos (cosine 0) = 2*Real.pi/3 := by
  have hcos : Real.cos (2*Real.pi/3) = -(1/2 : ℝ) := by
    rw [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]
  rw [cosine_zero,← hcos]
  exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Article: the critical wave multiplier is a cubic root of unity. -/
theorem critical_wave_cube : z 0 (Real.arccos (cosine 0))^3 = 1 := by
  rw [z_pow,angle_zero]
  convert Complex.exp_two_pi_mul_I using 1
  push_cast
  ring

/-- Article: this cubic root is nontrivial, so the cycle is not stationary. -/
theorem critical_wave_ne_one : z 0 (Real.arccos (cosine 0)) ≠ 1 := by
  intro h
  have hr := congrArg Complex.re h
  have hz := z_pow_re 0 (Real.arccos (cosine 0)) 1
  simp only [Nat.cast_one,one_mul,mul_zero,Real.exp_zero,one_mul,pow_one] at hz
  have hcos := Real.cos_arccos (cosine_mem 0).1 (cosine_mem 0).2
  rw [hcos,cosine_zero] at hz
  rw [cosine_zero,hz] at hr
  norm_num at hr

/-- Article: every critical planar wave position repeats after exactly three steps. -/
theorem critical_wave_period (k : ℕ) :
    z 0 (Real.arccos (cosine 0))^(k+3) = z 0 (Real.arccos (cosine 0))^k := by
  rw [pow_add,critical_wave_cube,mul_one]

/-- Article: the singleton finite-dimensional critical wave also has period three. -/
theorem finitePosition_period (k : ℕ) :
    finitePosition (fun _ : Fin 1 => (1 : NNReal)) (fun _ => atom 0) 0 (some (k+3)) =
      finitePosition (fun _ : Fin 1 => (1 : NNReal)) (fun _ => atom 0) 0 (some k) := by
  ext j
  simp only [finitePosition_apply,NNReal.coe_one,Real.sqrt_one,one_smul]
  exact critical_wave_period k

/-- Article: the three-cycle at t=0 attains the upper strip boundary v=logφ. -/
theorem critical_feasible :
    Feasible (Real.log Real.goldenRatio) 0 (spectrum 0) 0 := by
  have h := actual_feasible Threshold.criticalQ_pos Threshold.criticalQ_lt_one
  rw [factor_critical,Real.log_one,valueConstant_zero] at h
  have hl : Real.log Threshold.criticalQ = -Real.log Real.goldenRatio := Real.log_inv _
  rw [hl,sub_neg_eq_add,zero_add] at h
  exact h

end polyak.Spiral
