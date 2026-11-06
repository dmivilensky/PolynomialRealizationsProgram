import nesterov.Layer.SpreadWitnessScale

/-! The two source little-o assumptions imply the literal quantitative
smallness conditions of the half-step spreading lemma. -/
namespace nesterov.TwoStep.Spread
noncomputable section
open Filter Set
open scoped Topology

theorem spread_smallness_of_cubic {A : Type*} {l : Filter A} {ε M ω₀ : A→ℝ}
    {ck s c α η C : ℝ} (hck : 0<ck) (hs : s∈Ioc (0:ℝ) (1/6))
    (hc : 0<c) (hα : 0<α) (hη : 0<η)
    (he : Tendsto ε l (𝓝 0)) (hep : ∀ᶠ a in l,0<ε a)
    (hM : ∀ᶠ a in l,0≤M a)
    (hω₀ : ∀ᶠ a in l,ω₀ a∈Ioc (0:ℝ) (2*Real.pi/3))
    (hεscale : Tendsto (fun a=>ε a/cubicScale (xiMax s (ω₀ a))) l (𝓝 0))
    (hMscale : Tendsto (fun a=>M a/cubicScale (xiMax s (ω₀ a))) l (𝓝 0)) :
    ∀ᶠ a in l,
      Real.pi^2*M a/(α*ω₀ a)≤bandMargin ck s (ω₀ a)/2 ∧
      C*(|Real.log (1-c*ε a)|/(bandMargin ck s (ω₀ a)*(s*ω₀ a)))^2+
        Real.pi^2*M a/(α*ω₀ a)<Real.sqrt η/8 := by
  let x : A→ℝ := fun a=>xiMax s (ω₀ a)
  let m : A→ℝ := fun a=>bandMargin ck s (ω₀ a)
  let d : A→ℝ := fun a=>Real.pi^2*M a/(α*ω₀ a)
  have hδ := marginFactor_pos hck hs.1
  have hxp : ∀ᶠ a in l,0<x a := hω₀.mono fun _ ha=>xiMax_pos hs ha
  have hmp : ∀ᶠ a in l,0<m a := hω₀.mono fun _ ha=>bandMargin_pos hck hs.1 ha.1
  have hden : ∀ᶠ a in l,marginFactor ck s*cubicScale (x a)≤m a*ω₀ a := by
    filter_upwards [hω₀] with a ha
    exact margin_frequency_lower hck hs.1 ha.1 (xiMax_pos hs ha).le
      (by dsimp [x,xiMax];linarith [Real.neg_one_le_cos ((1+s)*ω₀ a)])
      (xiMax_le_square hs ha.1)
  have hp : ∀ᶠ a in l,0<cubicScale (x a) := hxp.mono fun _ ha=>cubicScale_pos ha
  have hMratio := ratio_tendsto_of_denominator_lower hδ hM hp hden hMscale
  have hεratio := ratio_tendsto_of_denominator_lower hδ (hep.mono fun _ ha=>ha.le) hp hden hεscale
  have hdratio : Tendsto (fun a=>d a/m a) l (𝓝 0) := by
    apply (show Tendsto (fun a=>(Real.pi^2/α)*(M a/(m a*ω₀ a))) l (𝓝 0) by
      simpa only [mul_zero] using hMratio.const_mul (Real.pi^2/α)).congr'
    exact Eventually.of_forall fun a=>by
      dsimp [d]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
  have hdp : ∀ᶠ a in l,0≤d a := by
    filter_upwards [hM,hω₀] with a hM ha
    exact div_nonneg (mul_nonneg (sq_nonneg _) hM) (mul_pos hα ha.1).le
  have hdlim : Tendsto d l (𝓝 0) := by
    have hupper : ∀ᶠ a in l,d a≤(1/4)*(d a/m a) := by
      filter_upwards [hdp,hmp] with a hd hm
      have hmq : m a≤1/4 := min_le_left _ _
      calc
        _=(d a/m a)*m a := (div_mul_cancel₀ _ hm.ne').symm
        _≤(d a/m a)*(1/4) := mul_le_mul_of_nonneg_left hmq (div_nonneg hd hm.le)
        _=_ := by ring
    exact squeeze_zero' hdp hupper (by simpa only [mul_zero] using hdratio.const_mul (1/4))
  have hsmall : ∀ᶠ a in l,c*ε a≤1/2 := by
    have hh : Tendsto (fun a=>c*ε a) l (𝓝 0) := by simpa only [mul_zero] using he.const_mul c
    exact (hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))).mono fun _ ha=>ha.le
  have hloglim : Tendsto (fun a=>|Real.log (1-c*ε a)|/(m a*(s*ω₀ a))) l (𝓝 0) := by
    have hupper : ∀ᶠ a in l,
        |Real.log (1-c*ε a)|/(m a*(s*ω₀ a))≤(2*c/s)*(ε a/(m a*ω₀ a)) := by
      filter_upwards [hsmall,hep,hmp,hω₀] with a hsmall he hm hω
      calc
        _≤(2*c*ε a)/(m a*(s*ω₀ a)) := div_le_div_of_nonneg_right
          (abs_log_radius_bound hc he hsmall) (by positivity [hs.1,hω.1])
        _=_ := by simp only [div_eq_mul_inv,mul_inv_rev];ring
    have hlower : ∀ᶠ a in l,0≤|Real.log (1-c*ε a)|/(m a*(s*ω₀ a)) := by
      filter_upwards [hmp,hω₀] with a hm hω
      exact div_nonneg (abs_nonneg _) (by positivity [hs.1,hω.1])
    exact squeeze_zero' hlower hupper
      (by simpa only [mul_zero] using hεratio.const_mul (2*c/s))
  have herr : Tendsto (fun a=>C*(|Real.log (1-c*ε a)|/(m a*(s*ω₀ a)))^2+d a) l (𝓝 0) := by
    simpa only [zero_pow (by omega : 2≠0),mul_zero,zero_add] using
      ((hloglim.pow 2).const_mul C).add hdlim
  filter_upwards [hmp,hdratio.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)),
    herr.eventually (eventually_lt_nhds (by positivity : (0:ℝ)<Real.sqrt η/8))]
    with a hm hd herr
  constructor
  · change d a≤m a/2
    linarith [((div_lt_iff₀ hm).mp hd).le]
  · exact herr

end
end nesterov.TwoStep.Spread
