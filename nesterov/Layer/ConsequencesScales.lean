import nesterov.Layer.Model
import nesterov.Layer.RationalScale
import nesterov.Slow.Kappa

/-! The literal condition-number powers in the layer definition and scale table. -/
namespace nesterov.Layer
noncomputable section
open Filter Set
open scoped Topology

theorem kappa_epsilon_half {κ : ℝ} (hκ : 0<κ) :
    Slow.epsilon κ=κ^(-1/2:ℝ) := by
  unfold Slow.epsilon
  rw [one_div,Real.sqrt_eq_rpow,←Real.rpow_neg hκ.le]
  norm_num

theorem kappa_epsilon_quarter {κ : ℝ} (hκ : 0<κ) :
    Real.sqrt (Slow.epsilon κ)=κ^(-1/4:ℝ) := by
  rw [kappa_epsilon_half hκ,Real.sqrt_eq_rpow,←Real.rpow_mul hκ.le]
  norm_num

theorem kappa_epsilon_eighth {κ : ℝ} (hκ : 0<κ) :
    Real.sqrt (Real.sqrt (Slow.epsilon κ))=κ^(-1/8:ℝ) := by
  rw [kappa_epsilon_quarter hκ,Real.sqrt_eq_rpow,←Real.rpow_mul hκ.le]
  norm_num

theorem kappa_deficit_identity {κ τ : ℝ} (hκ : 0<κ) :
    (1/2-τ)/Real.sqrt (Slow.epsilon κ)=κ^(1/4:ℝ)*(1/2-τ) := by
  rw [kappa_epsilon_quarter hκ,show (-1/4:ℝ)= -(1/4:ℝ) by ring,Real.rpow_neg hκ.le,
    div_inv_eq_mul,mul_comm]

theorem kappa_half_step_identity {κ τ : ℝ} (hκ : 0<κ) :
    τ=1/2-((1/2-τ)/Real.sqrt (Slow.epsilon κ))*κ^(-1/4:ℝ) := by
  rw [←kappa_epsilon_quarter hκ]
  have hs : Real.sqrt (Slow.epsilon κ)≠0 :=
    (Real.sqrt_pos.mpr (one_div_pos.mpr (Real.sqrt_pos.mpr hκ))).ne'
  rw [div_mul_cancel₀ _ hs]
  ring

theorem kappa_layer_scale_tendsto :
    Tendsto (fun κ=>Real.sqrt (Slow.epsilon κ)) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Real.sqrt_zero] using
      (Slow.epsilon_tendsto.mono_right nhdsWithin_le_nhds).sqrt
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
    exact Real.sqrt_pos.mpr (one_div_pos.mpr (Real.sqrt_pos.mpr hκ))

theorem rationalPeriod_kappa {φ : ℝ} (hφ : 0<φ) :
    Tendsto (fun κ=>(rationalPeriod φ (Real.sqrt (Slow.epsilon κ)):ℝ)/κ^(1/8:ℝ)) atTop
      (𝓝 (Real.pi*Real.sqrt (2/φ))) := by
  apply ((rationalPeriod_scaled_tendsto hφ).comp kappa_layer_scale_tendsto).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  change (rationalPeriod φ (Real.sqrt (Slow.epsilon κ)):ℝ)*Real.sqrt (Real.sqrt (Slow.epsilon κ))=_
  rw [kappa_epsilon_eighth hκ,show (-1/8:ℝ)= -(1/8:ℝ) by ring,
    Real.rpow_neg hκ.le]
  simp only [div_eq_mul_inv]

theorem rationalAngle_kappa {φ : ℝ} (hφ : 0<φ) :
    Tendsto (fun κ=>rationalAngle φ (Real.sqrt (Slow.epsilon κ))*κ^(1/8:ℝ)) atTop
      (𝓝 (Real.sqrt (2*φ))) := by
  have he : (2:ℝ)/Real.sqrt (2/φ)=Real.sqrt (2*φ) := by
    apply (div_eq_iff (Real.sqrt_pos.mpr (div_pos (by norm_num) hφ)).ne').mpr
    have hp : (2*φ)*(2/φ)=(4:ℝ) := by field_simp;norm_num
    have hh := Real.sqrt_mul (show 0≤2*φ by positivity) (2/φ)
    rw [hp] at hh
    rw [show Real.sqrt (4:ℝ)=2 by norm_num] at hh
    exact hh
  have ht := (rationalAngle_scaled_tendsto hφ).comp kappa_layer_scale_tendsto
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  change rationalAngle φ (Real.sqrt (Slow.epsilon κ))/Real.sqrt (Real.sqrt (Slow.epsilon κ))=_
  rw [kappa_epsilon_eighth hκ,show (-1/8:ℝ)= -(1/8:ℝ) by ring,
    Real.rpow_neg hκ.le]
  simp only [div_inv_eq_mul]

theorem rationalXi_kappa {φ : ℝ} (hφ : 0<φ) :
    Tendsto (fun κ=>rationalXi φ (Real.sqrt (Slow.epsilon κ))*κ^(1/4:ℝ)) atTop (𝓝 φ) := by
  apply ((rationalXi_scaled_tendsto hφ).comp kappa_layer_scale_tendsto).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  change rationalXi φ (Real.sqrt (Slow.epsilon κ))/Real.sqrt (Slow.epsilon κ)=_
  rw [kappa_epsilon_quarter hκ,show (-1/4:ℝ)= -(1/4:ℝ) by ring,
    Real.rpow_neg hκ.le,div_inv_eq_mul]

end
end nesterov.Layer
