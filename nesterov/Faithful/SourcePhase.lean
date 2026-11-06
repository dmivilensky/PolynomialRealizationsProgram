import nesterov.Faithful.LowLimits
import nesterov.Faithful.FamilyResonance

/-! Exact dictionaries from the analytic limit-phase model to the source method. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set Spectral Phase
open scoped Topology NNReal

theorem limitProduct_characteristic (M : StationaryMethod) (q : Polynomial ℝ)
    (hfactor : M.recurrencePolynomial=(X-C 1)^2*q) (ω : ℝ) :
    limitProduct M.queryPolynomial q ω=
      M.characteristic 0 (circle ω)*star (M.characteristic 1 (circle ω)) := by
  have hv : evalComplex M.recurrencePolynomial (circle ω)=(circle ω-1)^2*evalComplex q (circle ω) := by
    rw [hfactor]
    simp [evalComplex]
  simp only [M.characteristic_eq_polynomial_eval,eval_sub,eval_mul,eval_C,
    Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,sub_zero]
  change limitProduct M.queryPolynomial q ω=
    evalComplex M.recurrencePolynomial (circle ω)*
      star (evalComplex M.recurrencePolynomial (circle ω)-evalComplex M.queryPolynomial (circle ω))
  rw [hv]
  unfold limitProduct
  rw [show (circle ω-1)^2*evalComplex q (circle ω)-evalComplex M.queryPolynomial (circle ω)=
    -(evalComplex M.queryPolynomial (circle ω)-(circle ω-1)^2*evalComplex q (circle ω)) by ring,star_neg]
  ring

theorem stationary_limit_angle (M : StationaryMethod) (q : Polynomial ℝ)
    (hfactor : M.recurrencePolynomial=(X-C 1)^2*q) (c : Frequency) :
    angle (g (M.symbolPair 0 1 0) c) (skew (M.symbolPair 0 1 0) c)=
      limitAngle M.queryPolynomial q (Real.arccos c) := by
  have hf := Phase.stationary_factor M (μ:=0) (L:=1) (by norm_num) 0 c
  have hz : polyak.Waves.z 0 (Real.arccos c)=circle (Real.arccos c) := by simp [polyak.Waves.z,circle]
  rw [hz] at hf
  simp only [mul_assoc] at hf
  rw [←limitProduct_characteristic M q hfactor] at hf
  have he : mode (g (M.symbolPair 0 1 0) c) (skew (M.symbolPair 0 1 0) c)=
      (4:ℝ)*(-star (limitProduct M.queryPolynomial q (Real.arccos c))) := by
    have hh := congrArg star hf
    unfold mode
    convert hh using 1 <;> simp
    ring
  unfold angle limitAngle
  rw [he,Complex.arg_real_mul _ (by norm_num : (0:ℝ)<4)]

variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

theorem family_limit_angle (c : Frequency) :
    angle (g (familyPair F 0) c) (skew (familyPair F 0) c)=
      limitAngle (F.u 0) F.q0 (Real.arccos c) := by
  have hf := Phase.stationary_factor (F.method 0) (μ:=0) (L:=1) (by norm_num) 0 c
  have hz : polyak.Waves.z 0 (Real.arccos c)=circle (Real.arccos c) := by simp [polyak.Waves.z,circle]
  rw [hz] at hf
  simp only [mul_assoc] at hf
  rw [←limitProduct_characteristic (F.method 0) F.q0 F.initial_factor] at hf
  have he : mode (g (familyPair F 0) c) (skew (familyPair F 0) c)=
      (4:ℝ)*(-star (limitProduct (F.u 0) F.q0 (Real.arccos c))) := by
    have hh := congrArg star hf
    simp only [familyPair,zero_pow (by decide : 2≠0)]
    unfold mode
    convert hh using 1 <;> simp
    ring
  unfold angle limitAngle
  rw [he,Complex.arg_real_mul _ (by norm_num : (0:ℝ)<4)]

theorem limitProduct_eventually_ne_zero :
    ∀ᶠ ω in 𝓝[≠] (0:ℝ),limitProduct (F.u 0) F.q0 ω≠0 := by
  obtain ⟨X,hX,hX0,_,he⟩ := exists_product_germ (F.u 0) F.q0 F.step_pos (F.u_one 0) F.q0_one
  have hXne : X 0≠0 := by rw [hX0];exact div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr F.step_pos.ne')
  have hx := hX.continuousAt.tendsto.eventually (isOpen_compl_singleton.mem_nhds hXne)
  filter_upwards [hx.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with ω hXω hω
  rw [he]
  exact mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hω)) hXω

end
end nesterov.Faithful
