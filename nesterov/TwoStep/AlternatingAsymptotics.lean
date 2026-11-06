import nesterov.TwoStep.Alternating
import nesterov.TwoStep.QuadraticAsymptotics
import nesterov.Realization.RestQuadratic

/-! The stability-boundary alternating constant in the accelerated scaling. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def alternatingConstant (θ τ s : ℝ) : ℝ := (s-2*θ)*(1+2*τ)/(4*τ)

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def stabilityMargin (a : A) : ℝ := (4-(F.tuning a).stepSize*(1+2*(F.tuning a).tau))/F.epsilon a

theorem stability_gap_exact : ∀ᶠ a in l,
    largestCurvatureGap (F.tuning a)=
      (F.stabilityMargin a-2*F.thetaAt a)*F.epsilon a := by
  filter_upwards [F.epsilon_pos] with a ha
  rw [largestCurvatureGap_eq]
  unfold stabilityMargin thetaAt
  field_simp
  ring

theorem stability_gap_scaled_exact : ∀ᶠ a in l,
    largestCurvatureGap (F.tuning a)/F.epsilon a=F.stabilityMargin a-2*F.thetaAt a := by
  filter_upwards [F.stability_gap_exact,F.epsilon_pos] with a ha hp
  rw [ha,mul_div_cancel_right₀ _ hp.ne']

theorem boundary_S_tendsto (hboundary : y*(1+2*τ)=4) :
    Tendsto (fun a=>Quadratic.S (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize 1)
      l (𝓝 (-2/(1+2*τ))) := by
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).add F.beta_tendsto).sub
    ((F.step_tendsto.mul_const 1).mul ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto))
  have hden : 1+2*τ≠0 := ne_of_gt (by linarith [F.tau_nonneg])
  have hv : 1+1-y*1*(1+τ)=-2/(1+2*τ) := by
    apply (eq_div_iff hden).mpr
    linear_combination -(1+τ)*hboundary
  rw [hv] at hh
  convert hh using 1
  funext a
  rfl

theorem boundary_gap_tendsto (hboundary : y*(1+2*τ)=4) :
    Tendsto (fun a=>largestCurvatureGap (F.tuning a)) l (𝓝 0) := by
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).add F.beta_tendsto).const_mul 2 |>.sub
    (F.step_tendsto.mul ((tendsto_const_nhds (x:=(1:ℝ))).add (F.tau_tendsto.const_mul 2)))
  convert hh using 1
  · funext a
    exact largestCurvatureGap_eq _
  · rw [hboundary]
    norm_num

theorem gap_pos_of_stable (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ∀ᶠ a in l,0<largestCurvatureGap (F.tuning a) := by
  filter_upwards [hstable,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a hs ha ha1
  rw [largestCurvatureGap_eq]
  have hh := ((F.tuning a).stable_iff (sq_pos_of_pos ha) (by nlinarith : F.epsilon a^2<1)).mp hs
  simp only [mul_one] at hh
  linarith

/-- Lemma altmode(b), including the zero constant at the limiting stability threshold. -/
theorem alternating_shift_scaled_tendsto {s : ℝ} (hτ : 1/2≤τ)
    (hboundary : y*(1+2*τ)=4)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hs : Tendsto F.stabilityMargin l (𝓝 s)) :
    Tendsto (fun a=>alternatingShift (F.tuning a)/F.epsilon a)
      l (𝓝 (alternatingConstant θ τ s)) := by
  have hτpos : 0<τ := by linarith
  have hden : 0<1+2*τ := by linarith
  have hS₀ : -2/(1+2*τ)∈Ioo (-2:ℝ) 0 := by
    constructor
    · apply (lt_div_iff₀ hden).mpr
      linarith
    · exact div_neg_of_neg_of_pos (by norm_num) hden
  have hmode := alternating_mode_eventually (F.boundary_S_tendsto hboundary)
    (F.boundary_gap_tendsto hboundary) (F.gap_pos_of_stable hstable) hS₀
  have hgap : Tendsto (fun a=>largestCurvatureGap (F.tuning a)/F.epsilon a) l (𝓝 (s-2*θ)) := by
    apply (hs.sub (F.theta_tendsto.const_mul 2)).congr'
    filter_upwards [F.stability_gap_scaled_exact] with a ha
    exact ha.symm
  have ht := hmode.2.1.mul hgap
  have hlim : 1/(2+(-2/(1+2*τ)))*(s-2*θ)=alternatingConstant θ τ s := by
    unfold alternatingConstant
    field_simp
    ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [F.gap_pos_of_stable hstable] with a ha
  field_simp

/-- The alternating constant diverges when the scaled stability margin does. -/
theorem alternating_shift_scaled_atTop (hτ : 1/2≤τ) (hboundary : y*(1+2*τ)=4)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hs : Tendsto F.stabilityMargin l atTop) :
    Tendsto (fun a=>alternatingShift (F.tuning a)/F.epsilon a) l atTop := by
  have hden : 0<1+2*τ := by linarith
  have hσ : 0<2+(-2/(1+2*τ)) := by
    have hh : -2/(1+2*τ)>-2 := (lt_div_iff₀ hden).mpr (by linarith)
    linarith
  have hratio := alternatingDelta_ratio_tendsto (F.boundary_gap_tendsto hboundary)
    ((tendsto_const_nhds (x:=(2:ℝ))).add (F.boundary_S_tendsto hboundary)) hσ
    ((F.gap_pos_of_stable hstable).mono fun _ ha=>ha.ne')
  have hgap : Tendsto (fun a=>largestCurvatureGap (F.tuning a)/F.epsilon a) l atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [hs.eventually_ge_atTop (B+2*θ+1),
      F.theta_tendsto.eventually (eventually_lt_nhds (show θ<θ+1/2 by linarith)),
      F.stability_gap_scaled_exact] with a ha hθ heq
    change F.thetaAt a<θ+1/2 at hθ
    rw [heq]
    linarith
  have ht := hratio.pos_mul_atTop (one_div_pos.mpr hσ) hgap
  apply ht.congr'
  filter_upwards [F.gap_pos_of_stable hstable] with a ha
  dsimp [alternatingShift]
  field_simp

/-- Both literal rate notions see the largest-curvature alternating mode. -/
theorem alternating_rate_lower (hτ : 1/2≤τ) (hboundary : y*(1+2*τ)=4)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ∀ᶠ a in l,
      1-alternatingShift (F.tuning a)≤F.rate a ∧
      1-alternatingShift (F.tuning a)≤Momentum.momentumRestRate
        (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 ∧
      (1-F.rate a)/F.epsilon a≤alternatingShift (F.tuning a)/F.epsilon a := by
  have hden : 0<1+2*τ := by linarith
  have hS₀ : -2/(1+2*τ)∈Ioo (-2:ℝ) 0 := by
    constructor
    · apply (lt_div_iff₀ hden).mpr
      linarith
    · exact div_neg_of_neg_of_pos (by norm_num) hden
  have hmode := alternating_mode_eventually (F.boundary_S_tendsto hboundary)
    (F.boundary_gap_tendsto hboundary) (F.gap_pos_of_stable hstable) hS₀
  filter_upwards [hmode.2.2,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a ha he he1
  have hμ : 0<F.epsilon a^2 := sq_pos_of_pos he
  have hμL : F.epsilon a^2<1 := by nlinarith
  have hrad := ha.2.2.2.2.2.1
  have hq : 1-alternatingShift (F.tuning a)≤F.rate a := by
    obtain ⟨z,hz,hzrad⟩ := (Quadratic.scalarRadius_isGreatest (F.tuning a).beta
      (F.tuning a).tau (F.tuning a).stepSize 1).1
    rw [hrad] at hzrad
    rw [hzrad]
    exact Quadratic.root_norm_le_rate_general hμL.le ⟨hμL.le,le_rfl⟩ hz
  have hr := Momentum.scalarRadius_le_momentumRestRate (β:=(F.tuning a).beta) (τ:=(F.tuning a).tau)
    (F.tuning a).step_pos hμ hμL
    (lam:=1) ⟨hμL.le,le_rfl⟩
  rw [hrad] at hr
  refine ⟨hq,hr,?_⟩
  exact div_le_div_of_nonneg_right (by linarith) he.le

end Scaling
end
end nesterov.TwoStep
