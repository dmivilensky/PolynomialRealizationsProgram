import nesterov.Layer.SpreadWitnessSymbols
import nesterov.Layer.SpreadWitnessImaginary

/-! Actual two-step signs and phase defects on moving relative frequency bands. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Spectral Phase
open scoped Topology

namespace Spread

theorem continuous_frequency : Continuous frequency := by
  unfold frequency
  fun_prop

theorem continuous_magnitude (a : SymbolPair) :
    Continuous (fun ω=>magnitude (g a (frequency ω)) (skew a (frequency ω))) := by
  have hg := (continuous_g a).comp continuous_frequency
  have hs := (continuous_skew a).comp continuous_frequency
  unfold magnitude mode
  fun_prop

theorem continuousOn_phase (a : SymbolPair) {B : Set ℝ}
    (hg : ∀ ω∈B,0<g a (frequency ω)) :
    ContinuousOn (fun ω=>angle (g a (frequency ω)) (skew a (frequency ω))) B := by
  have hgC := (continuous_g a).comp continuous_frequency
  have hsC := (continuous_skew a).comp continuous_frequency
  have hc : Continuous (fun ω=>mode (g a (frequency ω)) (skew a (frequency ω))) := by
    unfold mode
    fun_prop
  intro ω hω
  exact (Complex.continuousAt_arg (Or.inl (by simpa only [mode_re] using hg ω hω))).comp_continuousWithinAt
    hc.continuousWithinAt

end Spread

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem spread_bracket_eventually_lower {c : ℝ} (hc : c<θ/2) :
    ∀ᶠ a in l, ∀ ω : ℝ,
      2*(F.tuning a).tau*(1-c*F.epsilon a)*(1-Real.cos ω)≤
        mixedBracket (F.tuning a).beta (F.tuning a).tau (1-c*F.epsilon a) (1-Real.cos ω) := by
  filter_upwards [F.epsilon_pos,F.beta_eq,
    F.theta_tendsto.eventually (eventually_gt_nhds (show 2*c<θ by linarith))]
    with a he hb hθ ω
  change 2*c<F.thetaAt a at hθ
  have heq : mixedBracket (F.tuning a).beta (F.tuning a).tau
      (1-c*F.epsilon a) (1-Real.cos ω)=
      F.epsilon a*(F.thetaAt a-2*c)+(1+(F.tuning a).tau)*c^2*F.epsilon a^2+
        2*(F.tuning a).tau*(1-c*F.epsilon a)*(1-Real.cos ω) := by
    rw [hb]
    unfold mixedBracket
    ring
  rw [heq]
  have hτ := (F.tuning a).tau_nonneg
  have hp : 0≤F.epsilon a*(F.thetaAt a-2*c) := mul_nonneg he.le (by linarith)
  have hq : 0≤(1+(F.tuning a).tau)*c^2*F.epsilon a^2 := by positivity
  linarith

theorem spread_product_real_eventually_le {c s : ℝ} {ω₀ M : A→ℝ}
    (hc : c<θ/2) (hτ : 0<τ) (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : ∀ᶠ a in l,ω₀ a∈Ioc (0:ℝ) (2*Real.pi/3))
    (hM : ∀ᶠ a in l,∀ ω∈Spread.band s (ω₀ a),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤M a)
    (hsmall : Tendsto (fun a=>M a/Spread.xiMax s (ω₀ a)) l (𝓝 0)) :
    ∃ α : ℝ,0<α ∧ ∀ᶠ a in l,∀ ω∈Spread.band s (ω₀ a),
      (Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω).re≤
        -α*(1-Real.cos ω) := by
  let α : ℝ := Spread.endpointReserve*y*τ/4
  have hα : 0<α := by
    dsimp [α]
    exact div_pos (mul_pos (mul_pos Spread.endpointReserve_pos F.step_pos) hτ) (by norm_num)
  let D : A→ℝ := fun a=>2*Spread.endpointReserve*(F.tuning a).stepSize*
    (1-F.epsilon a^2)*(F.tuning a).tau*(1-c*F.epsilon a)^2
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  have he2 : Tendsto (fun a=>1-F.epsilon a^2) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.pow 2)
  have hD : Tendsto D l (𝓝 (2*Spread.endpointReserve*y*τ)) := by
    simpa only [one_pow,mul_one] using
      (((F.step_tendsto.const_mul (2*Spread.endpointReserve)).mul he2).mul F.tau_tendsto).mul (hr.pow 2)
  have hαD : 2*α<2*Spread.endpointReserve*y*τ := by
    dsimp [α]
    nlinarith [mul_pos (mul_pos Spread.endpointReserve_pos F.step_pos) hτ]
  refine ⟨α,hα,?_⟩
  filter_upwards [hω₀,hM,hsmall.eventually (eventually_lt_nhds (half_pos hα)),
    F.spread_bracket_eventually_lower hc,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hD.eventually (eventually_gt_nhds hαD)] with a hω₀ hM hm hbr he he1 hr hD ω hω
  have hmem := Spread.band_mem_Ioo hs hω₀ hω
  have hξ : 0<1-Real.cos ω := sub_pos.mpr (by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num : (0:ℝ)≤0) hmem.2.le hmem.1)
  have hxm := Spread.xiMax_pos hs hω₀
  have hcmp := (Spread.band_xi_comparable hs hω₀ hω).1
  have hMsmall : M a≤α*(1-Real.cos ω) := by
    have hh := (div_lt_iff₀ hxm).mp hm
    nlinarith [mul_le_mul_of_nonneg_left hcmp hα.le]
  have hP : mixedPolynomial (F.tuning a).beta (F.tuning a).tau
      ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
      (1-c*F.epsilon a) (1-Real.cos ω)≤M a :=
    (le_abs_self _).trans (hM ω hω)
  have hδ := Spread.band_two_sub_xi_lower hs hω₀ hω
  have htau := (F.tuning a).tau_nonneg
  have hstep := (F.tuning a).step_pos
  have hd : 0≤(F.tuning a).stepSize-(F.tuning a).stepSize*F.epsilon a^2 := by
    nlinarith [mul_nonneg hstep.le (show 0≤1-F.epsilon a^2 by nlinarith)]
  have htail : D a*(1-Real.cos ω)≤
      (2-(1-Real.cos ω))*((F.tuning a).stepSize-(F.tuning a).stepSize*F.epsilon a^2)*
        (1-c*F.epsilon a)*mixedBracket (F.tuning a).beta (F.tuning a).tau
          (1-c*F.epsilon a) (1-Real.cos ω) := by
    calc
      _=Spread.endpointReserve*
        (((F.tuning a).stepSize-(F.tuning a).stepSize*F.epsilon a^2)*(1-c*F.epsilon a)*
          (2*(F.tuning a).tau*(1-c*F.epsilon a)*(1-Real.cos ω))) := by dsimp [D];ring
      _≤(2-(1-Real.cos ω))*
        (((F.tuning a).stepSize-(F.tuning a).stepSize*F.epsilon a^2)*(1-c*F.epsilon a)*
          (2*(F.tuning a).tau*(1-c*F.epsilon a)*(1-Real.cos ω))) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
      _=((2-(1-Real.cos ω))*((F.tuning a).stepSize-(F.tuning a).stepSize*F.epsilon a^2)*
        (1-c*F.epsilon a))*(2*(F.tuning a).tau*(1-c*F.epsilon a)*(1-Real.cos ω)) := by ring
      _≤_ := mul_le_mul_of_nonneg_left (hbr ω) (by
        have hh : 0≤2-(1-Real.cos ω) := Spread.endpointReserve_pos.le.trans hδ
        positivity)
  have heq := Spread.product_re_mixed (F.tuning a) (μ:=F.epsilon a^2) (L:=1)
    (r:=1-c*F.epsilon a) hmem
  simp only [mul_one] at heq
  have hDξ := mul_le_mul_of_nonneg_right hD.le hξ.le
  linarith

end Scaling
end
end nesterov.TwoStep
