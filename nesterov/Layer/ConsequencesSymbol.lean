import nesterov.Layer.ConsequencesAlgebra
import nesterov.Layer.RationalScale
import nesterov.TwoStep.LimitSymbol
import nesterov.Layer.SymbolLimits

/-! The source sixth-order symbol coefficient is the actual half-wall symbol. -/
namespace nesterov.Layer
noncomputable section
open Filter Set
open scoped Topology

theorem sixth_order_symbol_exact {y : ℝ} (hy : 0<y) (ω : ℝ) :
    (TwoStep.limitData (1/2) y hy).symbol ω=s6 y*ω^6*(Real.sinc (ω/2))^6 := by
  rw [TwoStep.limitData_symbol,TwoStep.half_wall_symbol,one_sub_cos_sinc]
  unfold s6
  ring

theorem sixth_order_symbol_limit {y : ℝ} (hy : 0<y) :
    Tendsto (fun ω : ℝ=>(TwoStep.limitData (1/2) y hy).symbol ω/ω^6)
      (𝓝[≠] (0:ℝ)) (𝓝 (s6 y)) := by
  have harg : Tendsto (fun ω : ℝ=>ω/2) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun ω : ℝ=>ω) (𝓝[≠] (0:ℝ)) (𝓝 0) :=
      continuous_id.continuousWithinAt.tendsto
    simpa only [zero_div] using hid.div_const (2:ℝ)
  have hs := (Real.continuous_sinc.tendsto 0).comp harg
  have h := (hs.pow 6).const_mul (s6 y)
  simp only [Real.sinc_zero,one_pow,mul_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  have hne : ω≠0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hω
  simp only [Function.comp_def]
  rw [sixth_order_symbol_exact hy]
  field_simp

end
end nesterov.Layer

namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

/-- The literal H/(epsilon*xi) layer expansion on positive slow-frequency
coordinates. The undivided cubic's uniform limit also covers phi=0. -/
theorem layer_symbol_quotient_tendsto {B φ₀ : ℝ} {φ : A→ℝ} (c : ℝ)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) (hφ : Tendsto φ l (𝓝 φ₀)) (hφ₀ : 0<φ₀) :
    Tendsto (fun a=>F.layerCubic c a (Real.sqrt (F.epsilon a)*φ a)/
      (F.epsilon a*(Real.sqrt (F.epsilon a)*φ a))) l
      (𝓝 (Layer.polynomial θ y c B φ₀)) := by
  have h := (F.layer_cubic_tendsto c hB hφ).div hφ hφ₀.ne'
  rw [mul_div_cancel_left₀ _ hφ₀.ne'] at h
  convert h using 1
  funext a
  dsimp only [Pi.div_apply]
  rw [div_div]
  congr 1
  ring

theorem layer_symbol_quotient_uniform {B : ℝ} (c : ℝ)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) {K : Set ℝ} (hK : IsCompact K)
    (hpos : ∀ φ∈K,0<φ) :
    TendstoUniformlyOn (fun a φ=>F.layerCubic c a (Real.sqrt (F.epsilon a)*φ)/
      (F.epsilon a*(Real.sqrt (F.epsilon a)*φ)))
      (Layer.polynomial θ y c B) l K := by
  by_cases hne : K.Nonempty
  · obtain ⟨φ₀,hφ₀,hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    have hφ₀pos := hpos φ₀ hφ₀
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro e he
    have hu := Metric.tendstoUniformlyOn_iff.mp (F.layer_cubic_uniform c hB hK)
      (e*φ₀) (mul_pos he hφ₀pos)
    filter_upwards [hu,F.epsilon_pos] with a ha heps φ hφ
    have hφpos := hpos φ hφ
    have hden : Real.sqrt (F.epsilon a)≠0 := (Real.sqrt_pos.mpr heps).ne'
    have herror : F.layerCubic c a (Real.sqrt (F.epsilon a)*φ)/
        (F.epsilon a*(Real.sqrt (F.epsilon a)*φ))-Layer.polynomial θ y c B φ=
        (F.layerCubic c a (Real.sqrt (F.epsilon a)*φ)/
          (F.epsilon a*Real.sqrt (F.epsilon a))-φ*Layer.polynomial θ y c B φ)/φ := by
      field_simp [heps.ne',hden,hφpos.ne']
    rw [Real.dist_eq,abs_sub_comm,herror,abs_div,abs_of_pos hφpos]
    apply (div_lt_iff₀ hφpos).mpr
    have hh := ha φ hφ
    rw [Real.dist_eq,abs_sub_comm] at hh
    exact hh.trans_le (mul_le_mul_of_nonneg_left (hmin hφ) he.le)
  · have he : K=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he]
    exact tendstoUniformlyOn_empty

end
end nesterov.TwoStep.Scaling
