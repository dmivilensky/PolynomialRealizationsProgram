import nesterov.Layer.NegativeBandSymbols
import nesterov.Layer.NegativeBandScale
import nesterov.Layer.SpreadWitnessProduct

/-! The complete moving-band hypothesis package for the layer lower witness.
The bandwidth and all constants are fixed before epsilon. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ}

structure LayerNegativeBandData (F : Scaling A l θ y (1/2)) (c s₁ : ℝ) where
  s : ℝ
  s_pos : 0<s
  s_le : s≤s₁
  s_six : s≤1/6
  K : A→ℕ
  mixedBound : A→ℝ
  productBound : A→ℝ
  lagMargin : ℝ
  lagMargin_pos : 0<lagMargin
  periodScale : ℝ
  periodScale_pos : 0<periodScale
  period_scaled : Tendsto (fun a=>(K a:ℝ)*Real.sqrt (Real.sqrt (F.epsilon a))) l (𝓝 periodScale)
  epsilon_small : Tendsto (fun a=>F.epsilon a/
    Spread.cubicScale (Spread.xiMax s (2*Real.pi/K a))) l (𝓝 0)
  mixed_small : Tendsto (fun a=>mixedBound a/
    Spread.cubicScale (Spread.xiMax s (2*Real.pi/K a))) l (𝓝 0)
  bounds : ∀ᶠ a in l,3≤K a ∧ 0≤mixedBound a ∧ 0<productBound a ∧
    ∀ ω∈Spread.band s (2*Real.pi/K a),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤mixedBound a ∧
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤productBound a ∧
      ((1-circle (1-c*F.epsilon a) ω)*Spread.product (F.tuning a) (F.epsilon a^2) 1
        (1-c*F.epsilon a) ω).re≤ -lagMargin*F.epsilon a*productBound a

variable (F : Scaling A l θ y (1/2))

theorem layer_negative_band {B c s₁ : ℝ} (hy2 : y<2) (hBp : 0<B)
    (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hc : max (Layer.Lambda θ y B) 0/3<c) (hs₁ : 0<s₁) :
    Nonempty (LayerNegativeBandData F c s₁) := by
  obtain ⟨s,a,b,D,M,hs,ha,hab,hD,hM,hlo,hhi,hSymbols⟩ :=
    F.layer_negative_band_symbols hy2 hBp hB hc hs₁
  have hb : 0<b := ha.trans hab
  have hs6 : s∈Ioc (0:ℝ) (1/6) := ⟨hs.1,hs.2.trans (min_le_right _ _)⟩
  obtain ⟨C,hC,hProduct⟩ := F.layer_characteristic_product_bound c b hb
  have hgeo := F.layer_band_geometry hy2 hBp hs6 hlo hhi
  have hφ : 0<B*y/(2-y) := div_pos (mul_pos hBp F.step_pos) (by linarith)
  have hxlim : 0<(1+s)^2*(B*y/(2-y)) := mul_pos
    (sq_pos_of_pos (by linarith [hs.1])) hφ
  have hεsmall := F.layer_epsilon_div_cubic_tendsto hxlim hgeo.2
  let K : A→ℕ := F.layerPeriod B
  let Mfun : A→ℝ := fun p=>M*F.epsilon p
  let Xfun : A→ℝ := fun p=>C*Real.sqrt (F.epsilon p)
  refine ⟨{
    s := s
    s_pos := hs.1
    s_le := hs.2.trans (min_le_left _ _)
    s_six := hs6.2
    K := K
    mixedBound := Mfun
    productBound := Xfun
    lagMargin := D/C
    lagMargin_pos := div_pos hD hC
    periodScale := Real.pi*Real.sqrt (2/(B*y/(2-y)))
    periodScale_pos := by positivity
    period_scaled := (Layer.rationalPeriod_scaled_tendsto hφ).comp F.sqrt_epsilon_tendstoGT
    epsilon_small := hεsmall
    mixed_small := ?_
    bounds := ?_ }⟩
  · have ht := hεsmall.const_mul M
    simp only [mul_zero] at ht
    convert ht using 1
    funext p
    dsimp [Mfun,K]
    ring
  · have hK := F.sqrt_epsilon_tendstoGT.eventually (Layer.rationalPeriod_eventually_ge_three hφ)
    filter_upwards [hSymbols,hProduct,hK,F.epsilon_pos] with p hSymbols hProduct hK he
    refine ⟨hK,mul_nonneg hM.le he.le,mul_pos hC (Real.sqrt_pos.mpr he),?_⟩
    intro ω hω
    obtain ⟨hφmem,hMbound,hHbound⟩ := hSymbols ω hω
    refine ⟨hMbound,?_,?_⟩
    · apply hProduct ω
      exact (div_le_iff₀ (Real.sqrt_pos.mpr he)).mp hφmem.2
    · calc
        _≤ -D*F.epsilon p*Real.sqrt (F.epsilon p) := hHbound
        _= -(D/C)*F.epsilon p*Xfun p := by dsimp [Xfun];field_simp

end
end nesterov.TwoStep.Scaling
