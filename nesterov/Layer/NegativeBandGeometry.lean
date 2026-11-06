import nesterov.Layer.RationalScale
import nesterov.Layer.Resonance
import nesterov.Layer.SpreadWitnessGeometry
import nesterov.Layer.SpreadWitnessScale

/-! A fixed relative rational band remains inside any prescribed compact
neighborhood of the layer minimum. -/
namespace nesterov.Layer
noncomputable section
open Filter Set
open scoped Topology

theorem negative_interval {P : ℝ→ℝ} (hP : Continuous P) {φ s₁ : ℝ}
    (hφ : 0<φ) (hneg : P φ<0) (hs₁ : 0<s₁) :
    ∃ s a b m : ℝ,s∈Ioc (0:ℝ) (min s₁ (1/6)) ∧ 0<a ∧ a<b ∧ 0<m ∧
      a<(1-s)^2*φ ∧ (1+s)^2*φ<b ∧ ∀ x∈Icc a b,P x≤ -m := by
  have hnear : ∀ᶠ x in 𝓝 φ,P x<P φ/2 :=
    (hP.tendsto φ).eventually (eventually_lt_nhds (by linarith : P φ<P φ/2))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d : ℝ := min (δ/2) (φ/2)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  let a : ℝ := φ-d
  let b : ℝ := φ+d
  let m : ℝ := -(P φ)/2
  have ha : 0<a := by dsimp [a,d];linarith [min_le_right (δ/2) (φ/2)]
  have hab : a<b := by dsimp [a,b];linarith
  have hm : 0<m := by dsimp [m];linarith
  have hlow : Tendsto (fun s : ℝ=>(1-s)^2*φ) (𝓝[>] (0:ℝ)) (𝓝 φ) := by
    have hc : Continuous (fun s : ℝ=>(1-s)^2*φ) := by fun_prop
    simpa only [sub_zero,one_pow,one_mul] using (hc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have hupp : Tendsto (fun s : ℝ=>(1+s)^2*φ) (𝓝[>] (0:ℝ)) (𝓝 φ) := by
    have hc : Continuous (fun s : ℝ=>(1+s)^2*φ) := by fun_prop
    simpa only [add_zero,one_pow,one_mul] using (hc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have he : Tendsto (fun s : ℝ=>s) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hpos : ∀ᶠ s in 𝓝[>] (0:ℝ),0<s := self_mem_nhdsWithin
  obtain ⟨s,hs,hsmax,hlo,hup⟩ :=
    (hpos.and ((he.eventually (eventually_lt_nhds
      (show (0:ℝ)<min s₁ (1/6) from lt_min hs₁ (by norm_num)))).and
        ((hlow.eventually (eventually_gt_nhds (show a<φ by dsimp [a];linarith))).and
          (hupp.eventually (eventually_lt_nhds (show φ<b by dsimp [b];linarith)))))).exists
  refine ⟨s,a,b,m,⟨hs,hsmax.le⟩,ha,hab,hm,hlo,hup,?_⟩
  intro x hx
  have hdist : dist x φ<δ := by
    rw [Real.dist_eq]
    have hxd : |x-φ|≤d := abs_le.mpr ⟨by dsimp [a] at hx;linarith [hx.1],
      by dsimp [b] at hx;linarith [hx.2]⟩
    exact hxd.trans_lt (by dsimp [d];linarith [min_le_left (δ/2) (φ/2)])
  have hp := hball hdist
  change P x<P φ/2 at hp
  dsimp [m]
  linarith

end
end nesterov.Layer

namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

theorem layer_band_geometry {B s a b : ℝ} (hy2 : y<2) (hB : 0<B)
    (hs : s∈Ioc (0:ℝ) (1/6))
    (ha : a<(1-s)^2*(B*y/(2-y))) (hb : (1+s)^2*(B*y/(2-y))<b) :
    (∀ᶠ p in l,
      let ω₀ := 2*Real.pi/F.layerPeriod B p
      ω₀∈Ioc (0:ℝ) (2*Real.pi/3) ∧
      ∀ ω∈Spread.band s ω₀,(1-Real.cos ω)/Real.sqrt (F.epsilon p)∈Icc a b) ∧
    Tendsto (fun p=>Spread.xiMax s (2*Real.pi/F.layerPeriod B p)/Real.sqrt (F.epsilon p))
      l (𝓝 ((1+s)^2*(B*y/(2-y)))) := by
  let φ : ℝ := B*y/(2-y)
  have hφ : 0<φ := div_pos (mul_pos hB F.step_pos) (by linarith)
  have hlo := (Layer.rationalXi_multiple_scaled_tendsto hφ (1-s)).comp F.sqrt_epsilon_tendstoGT
  have hhi := (Layer.rationalXi_multiple_scaled_tendsto hφ (1+s)).comp F.sqrt_epsilon_tendstoGT
  have hK := F.sqrt_epsilon_tendstoGT.eventually (Layer.rationalPeriod_eventually_ge_three hφ)
  constructor
  · filter_upwards [hK,F.epsilon_pos,hlo.eventually (eventually_gt_nhds ha),
      hhi.eventually (eventually_lt_nhds hb)] with p hK he hlo hhi
    let ω₀ : ℝ := 2*Real.pi/F.layerPeriod B p
    have hK' : 3≤F.layerPeriod B p := hK
    have hKp : (0:ℝ)<F.layerPeriod B p := by exact_mod_cast (show 0<F.layerPeriod B p from by omega)
    have hωp : 0<ω₀ := div_pos (mul_pos (by norm_num) Real.pi_pos) hKp
    have hωhi : ω₀≤2*Real.pi/3 := by
      have hh : (3:ℝ)≤F.layerPeriod B p := by exact_mod_cast hK
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hh
    refine ⟨⟨hωp,hωhi⟩,?_⟩
    intro ω hω
    have hm := Spread.band_mem_Ioo hs ⟨hωp,hωhi⟩ hω
    have hlmem := Spread.band_mem_Ioo hs ⟨hωp,hωhi⟩
      (show (1-s)*ω₀∈Spread.band s ω₀ from ⟨le_rfl,by nlinarith [mul_pos hs.1 hωp]⟩)
    have humem := Spread.band_mem_Ioo hs ⟨hωp,hωhi⟩
      (show (1+s)*ω₀∈Spread.band s ω₀ from ⟨by nlinarith [mul_pos hs.1 hωp],le_rfl⟩)
    have hlcos := Real.cos_le_cos_of_nonneg_of_le_pi hlmem.1.le hm.2.le hω.1
    have hucos := Real.cos_le_cos_of_nonneg_of_le_pi hm.1.le humem.2.le hω.2
    have hlbound := div_le_div_of_nonneg_right (show 1-Real.cos ((1-s)*ω₀)≤1-Real.cos ω by linarith)
      (Real.sqrt_nonneg (F.epsilon p))
    have hubound := div_le_div_of_nonneg_right (show 1-Real.cos ω≤1-Real.cos ((1+s)*ω₀) by linarith)
      (Real.sqrt_nonneg (F.epsilon p))
    exact ⟨hlo.le.trans hlbound,hubound.trans hhi.le⟩
  · exact hhi

end
end nesterov.TwoStep.Scaling
