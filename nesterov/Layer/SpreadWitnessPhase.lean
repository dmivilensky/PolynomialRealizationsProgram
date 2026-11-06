import nesterov.Layer.SpreadWitnessBounds
import nesterov.Layer.SpreadWitnessScale

/-! Uniform half-step phase control from the source mixed-symbol bound. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set Spectral Phase
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem spread_phase_eventually {c s : ℝ} {ω₀ M : A→ℝ}
    (hc : c<θ/2) (hτ : 0<τ) (hs : s∈Ioc (0:ℝ) (1/6))
    (hω₀ : ∀ᶠ a in l,ω₀ a∈Ioc (0:ℝ) (2*Real.pi/3))
    (hM : ∀ᶠ a in l,∀ ω∈Spread.band s (ω₀ a),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤M a)
    (hsmall : Tendsto (fun a=>M a/Spread.xiMax s (ω₀ a)) l (𝓝 0)) :
    ∃ α : ℝ,0<α ∧ ∀ᶠ a in l,0≤M a ∧ ∀ ω∈Spread.band s (ω₀ a),
      0<g (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a)) (frequency ω) ∧
      0<skew (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a)) (frequency ω) ∧
      |ω-2*angle
        (g (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a)) (frequency ω))
        (skew (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a)) (frequency ω))|≤
          Real.pi^2*M a/(α*ω₀ a) := by
  obtain ⟨α,hα,hre⟩ := F.spread_product_real_eventually_le hc hτ hs hω₀ hM hsmall
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  refine ⟨α,hα,?_⟩
  filter_upwards [hre,hω₀,hM,F.spread_cross_im_eventually_pos hc,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
    with a hre hω₀ hM him he he1 hr
  have hcenter : ω₀ a∈Spread.band s (ω₀ a) := by
    constructor <;> nlinarith [mul_pos hs.1 hω₀.1]
  have hMpos : 0≤M a := (abs_nonneg _).trans (hM _ hcenter)
  refine ⟨hMpos,fun ω hω=>?_⟩
  have hmem := Spread.band_mem_Ioo hs hω₀ hω
  have hμL : F.epsilon a^2<1 := by nlinarith
  have hξ : 0<1-Real.cos ω := sub_pos.mpr (by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num : (0:ℝ)≤0) hmem.2.le hmem.1)
  let q := F.tuning a
  let r := 1-c*F.epsilon a
  let b := Spread.pair q (F.epsilon a^2) 1 r
  let ξ := 1-Real.cos ω
  let m := mixedPolynomial q.beta q.tau (q.stepSize*F.epsilon a^2) q.stepSize r ξ
  have hk := Spread.scale_pos q hμL
  have hcoord := Spread.coordinates q hμL hr ⟨hmem.1.le,hmem.2.le⟩
  have hreω := hre ω hω
  have himω := him ω hmem
  change 0<(Spread.product q (F.epsilon a^2) 1 r ω).im at himω
  have hg : Spread.scale q (F.epsilon a^2) 1*α*ξ≤g b (frequency ω) := by
    rw [hcoord.1]
    nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hreω)]
  have hg0 : 0<g b (frequency ω) := (mul_pos (mul_pos hk hα) hξ).trans_le hg
  have hs0 : 0<skew b (frequency ω) := by
    have hh := hcoord.2
    change 2*skew b (frequency ω)=Spread.scale q (F.epsilon a^2) 1*
      (Spread.product q (F.epsilon a^2) 1 r ω).im at hh
    nlinarith [mul_pos hk himω]
  have hmixed : ((1-Complex.exp ((ω:ℂ)*Complex.I))*Spread.product q
      (F.epsilon a^2) 1 r ω).re=ξ*m := by
    have hh := mixed_symbol q.beta q.tau (q.stepSize*F.epsilon a^2) (q.stepSize*1) r ω
    rw [mul_assoc,←Spread.product_normalized] at hh
    have hz : Complex.exp ((ω:ℂ)*Complex.I)=circle 1 ω := by simp [circle,polyak.Waves.z]
    simpa only [hz,mul_one] using hh
  have hphase := Spread.phase_defect_bound hmem hk hα hs0 hg
    (Spread.factor q hμL hr ⟨hmem.1.le,hmem.2.le⟩) hmixed
  have hωhalf : ω₀ a≤2*ω := by
    nlinarith [hω.1,mul_nonneg (show 0≤1/2-s by linarith [hs.2]) hω₀.1.le]
  have hm : |m|≤M a := hM ω hω
  have hnum : 0≤Real.pi^2*M a := mul_nonneg (sq_nonneg _) hMpos
  refine ⟨hg0,hs0,hphase.trans ?_⟩
  calc
    _≤Real.pi^2*M a/(2*α*ω) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm (sq_nonneg _)) (by positivity [hmem.1])
    _≤Real.pi^2*M a/(α*ω₀ a) := div_le_div_of_nonneg_left hnum
      (mul_pos hα hω₀.1) (by nlinarith [mul_le_mul_of_nonneg_left hωhalf hα.le])

end
end nesterov.TwoStep.Scaling
