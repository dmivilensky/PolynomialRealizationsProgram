import nesterov.Optimal.ModerateAlgebra
import nesterov.Optimal.NearCorner
import nesterov.Optimal.ProductScaleFamily
import nesterov.Optimal.P0Scale
import nesterov.Layer.SpreadWitness

/-! A moderate corner dip yields a genuine all-lag spread witness on its
variable rational band. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

theorem corner_moderate_band_rest_lower {q s : ℝ} {σ : A→ℝ} {K : A→ℕ}
    (hq : 0<q) (hq1 : q≤1) (hs0 : 0<s) (hs1 : s≤nesterov.Spread.canonicalKernel.s1)
    (hσ : Tendsto σ l (𝓝[>] (0:ℝ)))
    (hsmall : Tendsto (fun a=>F.epsilon a/σ a^2) l (𝓝 0))
    (hsd : ∀ᶠ a in l,σ a*F.cornerDefect a=1)
    (hD : ∀ᶠ a in l,q*(F.stabilityMargin a+5+F.cornerDefect a)≤F.cornerDefect a^2)
    (hK : ∀ᶠ a in l,3≤K a)
    (hband : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      (1-Real.cos ω)/σ a∈Icc (q/2) q)
    (hεscale : Tendsto (fun a=>F.epsilon a/Spread.cubicScale
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))) l (𝓝 0))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ∀ᶠ a in l,1-(1-q/48)*F.epsilon a≤Momentum.momentumRestRate
      (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  let c : ℝ := 1-q/48
  have hc0 : 0<c := by dsimp [c];linarith
  have hc1 : c<1 := by dsimp [c];linarith
  have hc : c<3/2 := by linarith
  have hσ0 := hσ.mono_right nhdsWithin_le_nhds
  have heσ : Tendsto (fun a=>F.epsilon a/σ a) l (𝓝 0) := by
    have h := hsmall.mul hσ0
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hσ.eventually self_mem_nhdsWithin] with a ha
    field_simp
  have hscale : ∀ᶠ a in l,F.epsilon a≤σ a := by
    filter_upwards [heσ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
      hσ.eventually self_mem_nhdsWithin] with a ha hs
    simpa only [one_mul] using ((div_lt_iff₀ hs).mp ha).le
  obtain ⟨C,hC,hprod⟩ := F.characteristic_product_bound_at_scale c q hq hscale
  let lam : ℝ := q^2/(64*C)
  have hlam : 0<lam := by dsimp [lam];positivity
  have hθ : Tendsto (fun a=>F.thetaAt a-3) l (𝓝 0) := by
    simpa only [thetaAt,sub_self] using F.theta_tendsto.sub_const 3
  have hθabs : Tendsto (fun a=>|F.thetaAt a-3|) l (𝓝 0) := by simpa using hθ.abs
  have hθsmall := hθabs.eventually (eventually_lt_nhds (by positivity : (0:ℝ)<q/192))
  have hpoly : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      q/2*σ a≤1-Real.cos ω ∧ 1-Real.cos ω≤q*σ a ∧
      |F.cornerNAt a (1-Real.cos ω)|≤100 ∧
      F.cornerNAt a (1-Real.cos ω)-4*c*(3-(1-Real.cos ω))≤ -q/8 := by
    filter_upwards [hband,hsd,hD,hθsmall,hσ.eventually self_mem_nhdsWithin,
      F.corner_denominator_pos hstable] with a ha hsd hD hθ hs hDen ω hω
    have hx := ha ω hω
    have hξ : 1-Real.cos ω∈Icc (0:ℝ) 2 :=
      ⟨by linarith [Real.cos_le_one ω],by linarith [Real.neg_one_le_cos ω]⟩
    have hd : 0<F.cornerDefect a := by nlinarith
    have hφ : F.cornerDefect a*(1-Real.cos ω)=(1-Real.cos ω)/σ a := by
      apply (eq_div_iff hs.ne').mpr
      calc
        F.cornerDefect a*(1-Real.cos ω)*σ a=(1-Real.cos ω)*(σ a*F.cornerDefect a) := by ring
        _=1-Real.cos ω := by rw [hsd,mul_one]
    have hlo : q/2≤F.cornerDefect a*(1-Real.cos ω) := by rw [hφ];exact hx.1
    have hhi : F.cornerDefect a*(1-Real.cos ω)≤q := by rw [hφ];exact hx.2
    refine ⟨(le_div_iff₀ hs).mp hx.1,(div_le_iff₀ hs).mp hx.2,?_,?_⟩
    · exact F.corner_moderate_N_bound a hq hq1 hd hDen.le hD hθ.le hξ hlo hhi
    · exact F.corner_moderate_dip_bound a hq hq1 hd hD hθ.le hξ hlo hhi
  have hcomp : IsCompact ({c}×ˢIcc (0:ℝ) 2) := isCompact_singleton.prod isCompact_Icc
  have htail := Metric.tendstoUniformlyOn_iff.mp (F.near_tail_error_uniform hcomp)
    (q/16) (by positivity)
  have hmix := Metric.tendstoUniformlyOn_iff.mp (F.near_mixed_error_uniform hcomp)
    1 (by norm_num)
  have hM : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤110*F.epsilon a := by
    filter_upwards [hpoly,hmix,F.near_mixed_exact c,F.layerMixed_actual c,F.epsilon_pos]
      with a hp hm hex hact he ω hω
    have hn := (hp ω hω).2.2.1
    have hξ : 1-Real.cos ω∈Icc (0:ℝ) 2 :=
      ⟨by linarith [Real.cos_le_one ω],by linarith [Real.neg_one_le_cos ω]⟩
    have herr : |F.nearMixedError c (1-Real.cos ω) a|≤1 := by
      have hh := hm (c,1-Real.cos ω) ⟨by simp,hξ⟩
      exact (by simpa only [Real.dist_eq,zero_sub,abs_neg] using hh.le)
    have ht : |2*c*(4-(1-Real.cos ω))|≤8 := by
      rw [abs_of_nonneg (mul_nonneg (by positivity : 0≤2*c)
        (by linarith [hξ.2] : 0≤4-(1-Real.cos ω)))]
      nlinarith [hξ.1,hξ.2]
    have hbound : |F.cornerNAt a (1-Real.cos ω)-2*c*(4-(1-Real.cos ω))+
        F.nearMixedError c (1-Real.cos ω) a|≤110 := by
      have h1 := abs_sub (F.cornerNAt a (1-Real.cos ω)) (2*c*(4-(1-Real.cos ω)))
      have h2 := abs_add_le (F.cornerNAt a (1-Real.cos ω)-2*c*(4-(1-Real.cos ω)))
        (F.nearMixedError c (1-Real.cos ω) a)
      linarith
    rw [hact]
    change |scaledQ0 _ _ _ _ _+scaledQ1 _ _ _ _ _*(1-Real.cos ω)+
      scaledQ2 _ _ _ _ _*(1-Real.cos ω)^2|≤_
    rw [hex,abs_mul,abs_of_pos he]
    nlinarith [mul_le_mul_of_nonneg_left hbound he.le]
  have hX : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤C*σ a := by
    filter_upwards [hprod,hpoly] with a ha hp ω hω
    exact ha ω (hp ω hω).2.1
  have hH : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      ((1-circle (1-c*F.epsilon a) ω)*Spread.product (F.tuning a)
        (F.epsilon a^2) 1 (1-c*F.epsilon a) ω).re≤ -lam*F.epsilon a*(C*σ a) := by
    have hp0 := (F.P0_at_scale_tendsto c hσ hsmall).eventually
      (eventually_lt_nhds (by positivity : (0:ℝ)<q^2/64))
    filter_upwards [hpoly,htail,F.near_tail_exact c,F.layerCubic_actual c,F.epsilon_pos,
      hσ.eventually self_mem_nhdsWithin,hp0] with a hp ht hex hact he hs hp0 ω hω
    have hξ : 1-Real.cos ω∈Icc (0:ℝ) 2 :=
      ⟨by linarith [Real.cos_le_one ω],by linarith [Real.neg_one_le_cos ω]⟩
    have herr : |F.nearTailError c (1-Real.cos ω) a|≤q/16 := by
      have hh := ht (c,1-Real.cos ω) ⟨by simp,hξ⟩
      exact (by simpa only [Real.dist_eq,zero_sub,abs_neg] using hh.le)
    have hneg : scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
        (F.tuning a).tau (1-Real.cos ω)≤ -(q/16)*F.epsilon a := by
      rw [hex]
      have hn := (hp ω hω).2.2.2
      nlinarith [(abs_le.mp herr).2]
    have htailneg := mul_le_mul_of_nonneg_left hneg hξ.1
    have hlow := (hp ω hω).1
    have hp0' := (div_lt_iff₀ (mul_pos he hs)).mp hp0
    rw [hact]
    unfold layerCubic
    have hlamid : lam*C=q^2/64 := by dsimp [lam];field_simp
    have hh : -lam*F.epsilon a*(C*σ a)= -(q^2/64)*F.epsilon a*σ a := by
      rw [show -lam*F.epsilon a*(C*σ a)= -(lam*C)*F.epsilon a*σ a by ring,hlamid]
    rw [hh]
    nlinarith [mul_le_mul_of_nonneg_right hlow (mul_nonneg (by positivity : 0≤q/16) he.le)]
  have hMs : Tendsto (fun a=>(110*F.epsilon a)/Spread.cubicScale
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))) l (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using hεscale.const_mul 110
  have hw := F.spread_witness hc0 hc (by norm_num : (0:ℝ)<1/2) hs0 hs1 hlam
    hstable hK hM hX hH hεscale hMs
  filter_upwards [hw] with a ha
  rcases ha with ⟨J,inst,w,z,hw,_,C,_,_,_,hrate⟩
  exact hrate

end
end nesterov.TwoStep.Scaling
