import nesterov.TwoStep.WallPeriodCounting

/-! A rational frequency at any vanishing positive xi scale. The chosen
integer period has the exact inverse-square-root leading constant. -/
namespace nesterov.Layer
noncomputable section
open Filter Set
open scoped Topology

theorem one_sub_cos_sinc (ω : ℝ) :
    1-Real.cos ω=ω^2/2*(Real.sinc (ω/2))^2 := by
  have hc := Real.cos_two_mul (ω/2)
  rw [show 2*(ω/2)=ω by ring] at hc
  have hs : Real.sin (ω/2)=(ω/2)*Real.sinc (ω/2) := by
    by_cases hω : ω=0
    · subst ω;simp
    · rw [Real.sinc_of_ne_zero (by exact div_ne_zero hω two_ne_zero)]
      field_simp
  have hh := Real.sin_sq_add_cos_sq (ω/2)
  rw [hs] at hh
  nlinarith

def rationalPeriod (φ ε : ℝ) : ℕ := TwoStep.largestBandPeriod φ ε
def rationalAngle (φ ε : ℝ) : ℝ := 2*Real.pi/rationalPeriod φ ε
def rationalXi (φ ε : ℝ) : ℝ := 1-Real.cos (rationalAngle φ ε)

theorem rationalPeriod_scaled_tendsto {φ : ℝ} (hφ : 0<φ) :
    Tendsto (fun ε : ℝ=>(rationalPeriod φ ε:ℝ)*Real.sqrt ε) (𝓝[>] (0:ℝ))
      (𝓝 (Real.pi*Real.sqrt (2/φ))) :=
  TwoStep.largestBandPeriod_scaled_tendsto hφ

theorem rationalPeriod_tendsto {φ : ℝ} (hφ : 0<φ) :
    Tendsto (rationalPeriod φ) (𝓝[>] (0:ℝ)) atTop :=
  TwoStep.largestBandPeriod_tendsto_atTop hφ

theorem rationalAngle_scaled_tendsto {φ : ℝ} (hφ : 0<φ) :
    Tendsto (fun ε : ℝ=>rationalAngle φ ε/Real.sqrt ε) (𝓝[>] (0:ℝ))
      (𝓝 (2/Real.sqrt (2/φ))) := by
  have hC : 0<Real.pi*Real.sqrt (2/φ) := by positivity
  have ht := (tendsto_const_nhds (x:=2*Real.pi)).div (rationalPeriod_scaled_tendsto hφ) hC.ne'
  have he : 2*Real.pi/(Real.pi*Real.sqrt (2/φ))=2/Real.sqrt (2/φ) := by
    field_simp
  rw [he] at ht
  convert ht using 1
  funext ε
  dsimp only [Pi.div_apply]
  unfold rationalAngle
  ring

theorem rationalAngle_tendsto {φ : ℝ} (hφ : 0<φ) :
    Tendsto (rationalAngle φ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hs : Tendsto (fun ε : ℝ=>Real.sqrt ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using he.sqrt
  have ht := (rationalAngle_scaled_tendsto hφ).mul hs
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hp : 0<ε := hε
  rw [div_mul_cancel₀ _ (Real.sqrt_pos.mpr hp).ne']

theorem rationalXi_scaled_tendsto {φ : ℝ} (hφ : 0<φ) :
    Tendsto (fun ε : ℝ=>rationalXi φ ε/ε) (𝓝[>] (0:ℝ)) (𝓝 φ) := by
  have hsinc : Tendsto (fun ε : ℝ=>Real.sinc (rationalAngle φ ε/2))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have ht : Tendsto (fun ε : ℝ=>rationalAngle φ ε/2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [zero_div] using (rationalAngle_tendsto hφ).div_const 2
    simpa only [Function.comp_def,Real.sinc_zero] using (Real.continuous_sinc.tendsto 0).comp ht
  have ht := ((rationalAngle_scaled_tendsto hφ).pow 2).div_const 2 |>.mul (hsinc.pow 2)
  have hv : (2/Real.sqrt (2/φ))^2/2*1^2=φ := by
    rw [div_pow,Real.sq_sqrt (by positivity : 0≤2/φ)]
    field_simp
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hp : 0<ε := hε
  rw [rationalXi,one_sub_cos_sinc,div_pow,Real.sq_sqrt hp.le]
  ring

theorem rationalXi_multiple_scaled_tendsto {φ : ℝ} (hφ : 0<φ) (b : ℝ) :
    Tendsto (fun ε : ℝ=>(1-Real.cos (b*rationalAngle φ ε))/ε) (𝓝[>] (0:ℝ))
      (𝓝 (b^2*φ)) := by
  have hsinc : Tendsto (fun ε : ℝ=>Real.sinc ((b*rationalAngle φ ε)/2))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have ht : Tendsto (fun ε : ℝ=>(b*rationalAngle φ ε)/2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [mul_zero,zero_div] using ((rationalAngle_tendsto hφ).const_mul b).div_const 2
    simpa only [Function.comp_def,Real.sinc_zero] using (Real.continuous_sinc.tendsto 0).comp ht
  have ht := (((rationalAngle_scaled_tendsto hφ).const_mul b).pow 2).div_const 2 |>.mul (hsinc.pow 2)
  have hv : (b*(2/Real.sqrt (2/φ)))^2/2*1^2=b^2*φ := by
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity : 0≤2/φ)]
    field_simp
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hp : 0<ε := hε
  rw [one_sub_cos_sinc,mul_div_assoc,mul_pow,div_pow,Real.sq_sqrt hp.le]
  ring

theorem rationalPeriod_eventually_ge_three {φ : ℝ} (hφ : 0<φ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),3≤rationalPeriod φ ε :=
  (rationalPeriod_tendsto hφ).eventually_ge_atTop 3

theorem rationalAngle_mem {φ ε : ℝ} (hK : 3≤rationalPeriod φ ε) :
    rationalAngle φ ε∈Ioo (0:ℝ) Real.pi := by
  simpa [rationalAngle,polyak.General.Regions.rationalAngle] using
    polyak.General.Regions.rationalAngle_mem (j:=1) (k:=rationalPeriod φ ε) le_rfl (by omega)

end
end nesterov.Layer
