import nesterov.Layer.NegativeBandGeometry

/-! Rational bands and cubic smallness at an arbitrary vanishing positive
frequency scale. These statements do not assume bounded corner coordinates. -/
namespace nesterov.Layer
noncomputable section
open Filter Set
open scoped Topology

theorem rational_band_geometry {A : Type*} {l : Filter A} {σ : A→ℝ}
    (hσ : Tendsto σ l (𝓝[>] (0:ℝ))) {φ s a b : ℝ} (hφ : 0<φ)
    (hs : s∈Ioc (0:ℝ) (1/6))
    (ha : a<(1-s)^2*φ) (hb : (1+s)^2*φ<b) :
    (∀ᶠ p in l,3≤rationalPeriod φ (σ p) ∧
      ∀ ω∈TwoStep.Spread.band s (2*Real.pi/rationalPeriod φ (σ p)),
        (1-Real.cos ω)/σ p∈Icc a b) ∧
    Tendsto (fun p=>TwoStep.Spread.xiMax s (2*Real.pi/rationalPeriod φ (σ p))/σ p)
      l (𝓝 ((1+s)^2*φ)) := by
  have hlo := (rationalXi_multiple_scaled_tendsto hφ (1-s)).comp hσ
  have hhi := (rationalXi_multiple_scaled_tendsto hφ (1+s)).comp hσ
  have hK := hσ.eventually (rationalPeriod_eventually_ge_three hφ)
  have hpos : ∀ᶠ p in l,0<σ p := hσ.eventually self_mem_nhdsWithin
  constructor
  · filter_upwards [hK,hpos,hlo.eventually (eventually_gt_nhds ha),
      hhi.eventually (eventually_lt_nhds hb)] with p hK he hlo hhi
    let ω₀ : ℝ := 2*Real.pi/rationalPeriod φ (σ p)
    have hKp : (0:ℝ)<rationalPeriod φ (σ p) := by
      exact_mod_cast (show 0<rationalPeriod φ (σ p) by omega)
    have hωp : 0<ω₀ := div_pos (mul_pos (by norm_num) Real.pi_pos) hKp
    have hωhi : ω₀≤2*Real.pi/3 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by exact_mod_cast hK)
    refine ⟨hK,?_⟩
    intro ω hω
    have hm := TwoStep.Spread.band_mem_Ioo hs ⟨hωp,hωhi⟩ hω
    have hlmem := TwoStep.Spread.band_mem_Ioo hs ⟨hωp,hωhi⟩
      (show (1-s)*ω₀∈TwoStep.Spread.band s ω₀ from
        ⟨le_rfl,by nlinarith [mul_pos hs.1 hωp]⟩)
    have humem := TwoStep.Spread.band_mem_Ioo hs ⟨hωp,hωhi⟩
      (show (1+s)*ω₀∈TwoStep.Spread.band s ω₀ from
        ⟨by nlinarith [mul_pos hs.1 hωp],le_rfl⟩)
    have hlcos := Real.cos_le_cos_of_nonneg_of_le_pi hlmem.1.le hm.2.le hω.1
    have hucos := Real.cos_le_cos_of_nonneg_of_le_pi hm.1.le humem.2.le hω.2
    have hlbound := div_le_div_of_nonneg_right
      (show 1-Real.cos ((1-s)*ω₀)≤1-Real.cos ω by linarith) he.le
    have hubound := div_le_div_of_nonneg_right
      (show 1-Real.cos ω≤1-Real.cos ((1+s)*ω₀) by linarith) he.le
    exact ⟨hlo.le.trans hlbound,hubound.trans hhi.le⟩
  · exact hhi

private theorem cubic_scale_identity {ε σ x : ℝ} (hσ : 0<σ) (hx : 0<x) :
    ε/TwoStep.Spread.cubicScale x=
      (ε/σ^2)*Real.sqrt σ/((x/σ)*Real.sqrt (x/σ)) := by
  rw [Real.sqrt_div hx.le]
  unfold TwoStep.Spread.cubicScale
  have hs := Real.sq_sqrt hσ.le
  field_simp
  rw [hs]

theorem epsilon_div_cubic_at_scale {A : Type*} {l : Filter A} {ε σ x : A→ℝ} {b : ℝ}
    (hσ : Tendsto σ l (𝓝[>] (0:ℝ))) (hb : 0<b)
    (hx : Tendsto (fun p=>x p/σ p) l (𝓝 b))
    (hε : Tendsto (fun p=>ε p/σ p^2) l (𝓝 0)) :
    Tendsto (fun p=>ε p/TwoStep.Spread.cubicScale (x p)) l (𝓝 0) := by
  have hsz := hσ.mono_right nhdsWithin_le_nhds
  have ht := (hε.mul hsz.sqrt).div (hx.mul hx.sqrt) (mul_pos hb (Real.sqrt_pos.mpr hb)).ne'
  simp only [Real.sqrt_zero,mul_zero,zero_div] at ht
  apply ht.congr'
  filter_upwards [hσ.eventually self_mem_nhdsWithin,hx.eventually (eventually_gt_nhds hb)]
    with p hs hp
  have hxp : 0<x p := (div_pos_iff_of_pos_right hs).mp hp
  exact (cubic_scale_identity hs hxp).symm

end
end nesterov.Layer
