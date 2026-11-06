import nesterov.Layer.NegativeBand
import nesterov.Layer.SpreadWitness
import nesterov.TwoStep.SequenceCeiling

/-! Theorem layer(b): finite-dimensional from-rest lower witnesses, with one
objective and start before every horizon, for the full source range of c. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology BigOperators NNReal

theorem RestLowerWitness.mono {q : Momentum.Tuning} {μ L r R : ℝ} {d : ℕ}
    (h : RestLowerWitness q μ L R d) (hr : 0≤r) (hrR : r≤R) :
    RestLowerWitness q μ L r d := by
  obtain ⟨f,x₀,hf,hx,c₀,hc₀,hbound⟩ := h
  refine ⟨f,x₀,hf,hx,c₀,hc₀,fun N=>?_⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrR N) hc₀.le) (norm_nonneg x₀)).trans (hbound N)

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

theorem layer_lower_small {B c : ℝ} (hy2 : y<2) (hBp : 0<B)
    (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hc : max (Layer.Lambda θ y B) 0/3<c) (hcθ : c<θ/2) :
    ∀ᶠ a in l, (∃ d : ℕ,RestLowerWitness (F.tuning a) (F.epsilon a^2) 1
      (1-c*F.epsilon a) d) ∧
      1-c*F.epsilon a≤Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  have hc0 : 0<c := (div_nonneg (le_max_right _ _) (by norm_num : (0:ℝ)≤3)).trans_lt hc
  obtain ⟨D⟩ := F.layer_negative_band hy2 hBp hB hc nesterov.Spread.canonicalKernel.s1_pos
  have hK : ∀ᶠ a in l,3≤D.K a := D.bounds.mono fun _ h=>h.1
  have hM : ∀ᶠ a in l,∀ ω∈Spread.band D.s (nesterov.Spread.centerAngle (D.K a)),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤D.mixedBound a := by
    filter_upwards [D.bounds] with a ha ω hω
    exact (ha.2.2.2 ω hω).1
  have hX : ∀ᶠ a in l,∀ ω∈Spread.band D.s (nesterov.Spread.centerAngle (D.K a)),
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤D.productBound a := by
    filter_upwards [D.bounds] with a ha ω hω
    exact (ha.2.2.2 ω hω).2.1
  have hH : ∀ᶠ a in l,∀ ω∈Spread.band D.s (nesterov.Spread.centerAngle (D.K a)),
      ((1-circle (1-c*F.epsilon a) ω)*Spread.product (F.tuning a) (F.epsilon a^2) 1
        (1-c*F.epsilon a) ω).re≤ -D.lagMargin*F.epsilon a*D.productBound a := by
    filter_upwards [D.bounds] with a ha ω hω
    exact (ha.2.2.2 ω hω).2.2
  have hw := F.spread_witness hc0 hcθ (by norm_num : (0:ℝ)<1/2)
    D.s_pos D.s_le D.lagMargin_pos hstable hK hM hX hH D.epsilon_small D.mixed_small
  filter_upwards [hw] with a ha
  obtain ⟨J,inst,w,q,hw,hband,C,hfeas,hreserve,hwitness,hrate⟩ := ha
  let : Fintype J := inst
  exact ⟨⟨2*Fintype.card J+1,hwitness⟩,hrate⟩

/-- All c above the source threshold are covered, including c≥θ/2. -/
theorem layer_lower {B c : ℝ} (hy2 : y<2) (hBp : 0<B)
    (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hc : max (Layer.Lambda θ y B) 0/3<c) :
    ∀ᶠ a in l, (∃ d : ℕ,RestLowerWitness (F.tuning a) (F.epsilon a^2) 1
      (1-c*F.epsilon a) d) ∧
      1-c*F.epsilon a≤Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  have hmax : max (Layer.Lambda θ y B) 0≤θ :=
    max_le (Layer.Lambda_le_theta F.step_pos hy2) F.theta_pos.le
  have hth : max (Layer.Lambda θ y B) 0/3<θ/2 := by linarith [F.theta_pos]
  obtain ⟨c',hc',hcmax⟩ := exists_between (lt_min hc hth)
  have hcc : c'<c := hcmax.trans_le (min_le_left _ _)
  have hct : c'<θ/2 := hcmax.trans_le (min_le_right _ _)
  have hc0 : 0<c := (div_nonneg (le_max_right _ _) (by norm_num : (0:ℝ)≤3)).trans_lt hc
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  filter_upwards [F.layer_lower_small hy2 hBp hB hstable hc' hct,F.epsilon_pos,
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with a ha he hr
  have hrad : 1-c*F.epsilon a≤1-c'*F.epsilon a := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcc.le) he.le]
  obtain ⟨d,hw⟩ := ha.1
  exact ⟨⟨d,hw.mono hr.le hrad⟩,hrad.trans ha.2⟩

theorem layer_rest_coefficient_eventually_le {B c : ℝ} (hy2 : y<2) (hBp : 0<B)
    (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hc : max (Layer.Lambda θ y B) 0/3<c) :
    ∀ᶠ a in l,F.restCoefficientAt a≤c := by
  filter_upwards [F.layer_lower hy2 hBp hB hstable hc,F.epsilon_pos] with a ha he
  apply (div_le_iff₀ he).mpr
  change 1-Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
    (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1≤c*F.epsilon a
  linarith [ha.2]

end Scaling
end
end nesterov.TwoStep
