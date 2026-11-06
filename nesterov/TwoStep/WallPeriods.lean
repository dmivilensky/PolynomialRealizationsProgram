import nesterov.TwoStep.Wall
import nesterov.TwoStep.Alternating

/-! Proposition periods: the explicit resonant band below the half-step wall. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def periodBandEdge (τ y : ℝ) : ℝ := y*(1-2*τ)/(2*(1-τ*y))
def periodLowerScale (θ τ ε : ℝ) : ℝ := θ*ε/(1-2*τ)

theorem periodBandEdge_mem {θ y τ : ℝ} (_hθ : 0<θ) (hy : 0<y)
    (hτ₀ : 0≤τ) (hτ : τ<1/2) (hmargin : y*(1+2*τ)<4) :
    τ*y<1 ∧ periodBandEdge τ y∈Ioo (0:ℝ) 2 := by
  have hden : 0<1+2*τ := by linarith
  have hty : τ*y≤4*τ/(1+2*τ) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmargin.le hτ₀]
  have hty1 : τ*y<1 := hty.trans_lt ((div_lt_one hden).mpr (by linarith))
  have hden2 : 0<2*(1-τ*y) := by linarith
  refine ⟨hty1,div_pos (mul_pos hy (by linarith)) hden2,?_⟩
  apply (div_lt_iff₀ hden2).mpr
  nlinarith

private def periodA0 (θ y ε : ℝ) : ℝ := A0 (1-θ*ε) (y*ε^2) y
private def periodA1 (θ y τ ε : ℝ) : ℝ := A1 (1-θ*ε) τ (y*ε^2) y
def periodA2 (θ y τ ε : ℝ) : ℝ := A2 (1-θ*ε) τ y

private theorem periodA0_scaled (θ y ε : ℝ) :
    periodA0 θ y ε=ε*(2*θ*y+ε*(y^2-2*θ*y*ε)) := by
  unfold periodA0 A0
  ring

private theorem periodA0_scaled_tendsto (θ y : ℝ) :
    Tendsto (fun ε : ℝ=>periodA0 θ y ε/ε) (𝓝[>] (0:ℝ)) (𝓝 (2*θ*y)) := by
  have ht : Tendsto (fun ε : ℝ=>2*θ*y+ε*(y^2-2*θ*y*ε)) (𝓝[>] (0:ℝ)) (𝓝 (2*θ*y)) := by
    simpa only [mul_zero,sub_zero,zero_mul,add_zero] using
      ((by fun_prop : Continuous (fun ε : ℝ=>2*θ*y+ε*(y^2-2*θ*y*ε))).tendsto 0).mono_left
        nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  rw [periodA0_scaled,mul_div_cancel_left₀ _ hε.ne']

private theorem periodA_limits (θ y τ : ℝ) :
    Tendsto (periodA0 θ y) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (periodA1 θ y τ) (𝓝[>] (0:ℝ)) (𝓝 (2*y*(2*τ-1))) ∧
    Tendsto (periodA2 θ y τ) (𝓝[>] (0:ℝ)) (𝓝 (4*(1-τ*y))) := by
  have h₀ : Continuous (periodA0 θ y) := by unfold periodA0 A0;fun_prop
  have h₁ : Continuous (periodA1 θ y τ) := by unfold periodA1 A1;fun_prop
  have h₂ : Continuous (periodA2 θ y τ) := by unfold periodA2 A2;fun_prop
  constructor
  · simpa [periodA0,A0] using h₀.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  constructor
  · convert h₁.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0) using 1
    congr 1
    unfold periodA1 A1
    ring
  · simpa [periodA2,A2] using h₂.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)

/-- The two actual real roots of the lag-one quadratic, with their two scales. -/
theorem period_band_roots {θ y τ : ℝ} (hθ : 0<θ) (hy : 0<y)
    (hτ₀ : 0≤τ) (hτ : τ<1/2) (hmargin : y*(1+2*τ)<4) :
    ∃ a b : ℝ→ℝ,
      Tendsto (fun ε=>a ε/ε) (𝓝[>] (0:ℝ)) (𝓝 (θ/(1-2*τ))) ∧
      Tendsto b (𝓝[>] (0:ℝ)) (𝓝 (periodBandEdge τ y)) ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),0<a ε ∧ a ε<b ε ∧
        ∀ ξ : ℝ,Ltau (1-θ*ε) τ (y*ε^2) y ξ=periodA2 θ y τ ε*(ξ-a ε)*(ξ-b ε) := by
  have hty := (periodBandEdge_mem hθ hy hτ₀ hτ hmargin).1
  have h2 : 0<4*(1-τ*y) := by linarith
  have h1 : 2*y*(2*τ-1)<0 := mul_neg_of_pos_of_neg (mul_pos (by norm_num) hy) (by linarith)
  obtain ⟨h₀,h₁,h₂⟩ := periodA_limits θ y τ
  let e : ℝ→ℝ := fun ε=>periodA0 θ y ε/periodA2 θ y τ ε
  let σ : ℝ→ℝ := fun ε=>-periodA1 θ y τ ε/periodA2 θ y τ ε
  let σ₀ : ℝ := -(2*y*(2*τ-1))/(4*(1-τ*y))
  have he : Tendsto e (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have ht := h₀.div h₂ h2.ne'
    simp only [zero_div] at ht
    convert ht using 1
  have hσ : Tendsto σ (𝓝[>] (0:ℝ)) (𝓝 σ₀) := h₁.neg.div h₂ h2.ne'
  have hσ₀ : 0<σ₀ := div_pos (neg_pos.mpr h1) h2
  have hσedge : σ₀=periodBandEdge τ y := by
    unfold σ₀ periodBandEdge
    field_simp
    ring
  let a : ℝ→ℝ := fun ε=>alternatingDelta (e ε) (σ ε)
  let b : ℝ→ℝ := fun ε=>σ ε-a ε
  have ha : Tendsto a (𝓝[>] (0:ℝ)) (𝓝 0) := alternatingDelta_tendsto he hσ hσ₀
  have hb : Tendsto b (𝓝[>] (0:ℝ)) (𝓝 (periodBandEdge τ y)) := by
    simpa only [sub_zero,hσedge] using hσ.sub ha
  have hA0 : ∀ᶠ ε in 𝓝[>] (0:ℝ),0<periodA0 θ y ε := by
    filter_upwards [self_mem_nhdsWithin,
      (periodA0_scaled_tendsto θ y).eventually (eventually_gt_nhds (mul_pos (mul_pos (by norm_num) hθ) hy))]
      with ε he hp
    change 0<ε at he
    exact ((div_pos_iff.mp hp).resolve_right (by rintro ⟨_,hh⟩;linarith)).1
  have hep : ∀ᶠ ε in 𝓝[>] (0:ℝ),0<e ε := by
    filter_upwards [hA0,h₂.eventually (eventually_gt_nhds h2)] with ε h₀ h₂
    exact div_pos h₀ h₂
  have hratio := alternatingDelta_ratio_tendsto he hσ hσ₀ (hep.mono fun _ h=>h.ne')
  have heps : Tendsto (fun ε : ℝ=>e ε/ε) (𝓝[>] (0:ℝ)) (𝓝 ((2*θ*y)/(4*(1-τ*y)))) := by
    have ht := (periodA0_scaled_tendsto θ y).div h₂ h2.ne'
    convert ht using 1
    funext ε
    dsimp [e]
    ring
  have hascale : Tendsto (fun ε : ℝ=>a ε/ε) (𝓝[>] (0:ℝ)) (𝓝 (θ/(1-2*τ))) := by
    have ht := hratio.mul heps
    have hv : 1/σ₀*((2*θ*y)/(4*(1-τ*y)))=θ/(1-2*τ) := by
      dsimp [σ₀]
      rw [one_div_div,div_mul_div_cancel₀' h2.ne']
      rw [show -(2*y*(2*τ-1))=(1-2*τ)*(2*y) by ring,
        show 2*θ*y=θ*(2*y) by ring]
      exact mul_div_mul_right _ _ (mul_ne_zero (by norm_num) hy.ne')
    rw [hv] at ht
    apply ht.congr'
    filter_upwards [hep] with ε hε
    dsimp [a]
    field_simp
  refine ⟨a,b,hascale,hb,?_⟩
  have hdisc : Tendsto (fun ε : ℝ=>(σ ε)^2-4*e ε) (𝓝[>] (0:ℝ)) (𝓝 (σ₀^2)) := by
    simpa only [mul_zero,sub_zero] using (hσ.pow 2).sub (he.const_mul 4)
  filter_upwards [hep,hσ.eventually (eventually_gt_nhds hσ₀),
    h₂.eventually (eventually_gt_nhds h2),hdisc.eventually (eventually_gt_nhds (sq_pos_of_pos hσ₀))]
    with ε he hσ hA₂ hdisc
  obtain ⟨hap,has,hroot⟩ := alternatingDelta_properties hσ he (by linarith : 4*e ε<(σ ε)^2)
  refine ⟨hap,by dsimp [b,a];linarith,?_⟩
  intro ξ
  have hroot' : periodA2 θ y τ ε*(a ε)^2+periodA1 θ y τ ε*a ε+periodA0 θ y ε=0 := by
    dsimp [e,σ] at hroot
    field_simp at hroot
    dsimp [a,e,σ]
    simp only [neg_div] at hroot ⊢
    linear_combination hroot
  have hbσ : periodA2 θ y τ ε*b ε=-periodA1 θ y τ ε-periodA2 θ y τ ε*a ε := by
    dsimp [b,σ]
    field_simp
  change periodA0 θ y ε+periodA1 θ y τ ε*ξ+periodA2 θ y τ ε*ξ^2=_
  linear_combination hroot'+ξ*hbσ-a ε*hbσ

/-- The complete three-interval sign assertion of Proposition periods. -/
theorem period_band_signs {θ y τ δ : ℝ} (hθ : 0<θ) (hy : 0<y)
    (hτ₀ : 0≤τ) (hτ : τ<1/2) (hmargin : y*(1+2*τ)<4) (hδ : δ∈Ioo (0:ℝ) (1/2)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (∀ ξ∈Icc ((1+δ)*periodLowerScale θ τ ε) ((1-δ)*periodBandEdge τ y),
        Ltau (1-θ*ε) τ (y*ε^2) y ξ<0) ∧
      (∀ ξ∈Ioc (0:ℝ) ((1-δ)*periodLowerScale θ τ ε),
        0<Ltau (1-θ*ε) τ (y*ε^2) y ξ) ∧
      (∀ ξ∈Icc ((1+δ)*periodBandEdge τ y) 2,
        0<Ltau (1-θ*ε) τ (y*ε^2) y ξ) := by
  obtain ⟨a,b,ha,hb,hroots⟩ := period_band_roots hθ hy hτ₀ hτ hmargin
  have hedge := (periodBandEdge_mem hθ hy hτ₀ hτ hmargin).2.1
  have hty := (periodBandEdge_mem hθ hy hτ₀ hτ hmargin).1
  have ht : 0<θ/(1-2*τ) := div_pos hθ (by linarith)
  have h2 : 0<4*(1-τ*y) := by linarith
  have h₂ := (periodA_limits θ y τ).2.2
  have hamin : (1-δ)*(θ/(1-2*τ))<θ/(1-2*τ) := by nlinarith [hδ.1]
  have hamax : θ/(1-2*τ)<(1+δ)*(θ/(1-2*τ)) := by nlinarith [hδ.1]
  have hbmin : (1-δ)*periodBandEdge τ y<periodBandEdge τ y := by nlinarith [hδ.1]
  have hbmax : periodBandEdge τ y<(1+δ)*periodBandEdge τ y := by nlinarith [hδ.1]
  filter_upwards [hroots,self_mem_nhdsWithin,h₂.eventually (eventually_gt_nhds h2),
    ha.eventually (eventually_gt_nhds hamin),ha.eventually (eventually_lt_nhds hamax),
    hb.eventually (eventually_gt_nhds hbmin),hb.eventually (eventually_lt_nhds hbmax)]
    with ε hroots he hA2 hal hau hbl hbu
  change 0<ε at he
  obtain ⟨_,hab,hfac⟩ := hroots
  have hls : periodLowerScale θ τ ε=(θ/(1-2*τ))*ε := by unfold periodLowerScale;ring
  have hal' : (1-δ)*periodLowerScale θ τ ε<a ε := by
    rw [hls]
    have hh := (lt_div_iff₀ he).mp hal
    nlinarith
  have hau' : a ε<(1+δ)*periodLowerScale θ τ ε := by
    rw [hls]
    have hh := (div_lt_iff₀ he).mp hau
    nlinarith
  constructor
  · intro ξ hξ
    rw [hfac ξ]
    exact mul_neg_of_pos_of_neg (mul_pos hA2 (sub_pos.mpr (hau'.trans_le hξ.1)))
      (sub_neg.mpr (hξ.2.trans_lt hbl))
  constructor
  · intro ξ hξ
    rw [hfac ξ]
    have hxa : ξ<a ε := hξ.2.trans_lt hal'
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hA2 (sub_neg.mpr hxa))
      (sub_neg.mpr (hxa.trans hab))
  · intro ξ hξ
    rw [hfac ξ]
    have hxb : b ε<ξ := hbu.trans_le hξ.1
    exact mul_pos (mul_pos hA2 (sub_pos.mpr (hab.trans hxb))) (sub_pos.mpr hxb)

end
end nesterov.TwoStep
