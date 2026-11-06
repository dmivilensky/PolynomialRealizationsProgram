import nesterov.TwoStep.SequenceCeiling
import nesterov.TwoStep.AlternatingAsymptotics
import nesterov.TwoStep.Kappa
import nesterov.FiniteCondition.Thresholds

/-! The zero-constant edge immediately after Proposition boundary. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology

/-- At the limiting stability threshold the actual full and rest factors are
strictly convergent, but both first-order acceleration coefficients vanish.
The parameter filter is arbitrary. -/
theorem zero_margin_filter {A : Type*} {l : Filter A} {θ y τ : ℝ}
    (F : Scaling A l θ y τ)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hτ : 1/2<τ) (hboundary : y*(1+2*τ)=4)
    (hs : Tendsto F.stabilityMargin l (𝓝 (2*θ))) :
    (∀ᶠ a in l,
      Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1 ∧
      Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1) ∧
      Tendsto F.fullCoefficientAt l (𝓝 0) ∧ Tendsto F.restCoefficientAt l (𝓝 0) := by
  have hconv : ∀ᶠ a in l,
      Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1 ∧
      Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1 := by
    filter_upwards [hstable,F.epsilon_pos,
      F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
      F.tau_tendsto.eventually (eventually_gt_nhds hτ)] with a hst he he1 ht
    have hμ := sq_pos_of_pos he
    have hμL : F.epsilon a^2<1 := by nlinarith
    have hr := FiniteCondition.half_step_converges (F.tuning a) hμ hμL hst ht.le
    exact ⟨hr,(Momentum.restRate_le_momentumRate (β:=(F.tuning a).beta)
      (τ:=(F.tuning a).tau) (F.tuning a).step_pos.ne' hμ hμL).trans_lt hr⟩
  have hshift : Tendsto (fun a=>alternatingShift (F.tuning a)/F.epsilon a) l (𝓝 0) := by
    simpa only [alternatingConstant,sub_self,zero_mul,zero_div] using
      F.alternating_shift_scaled_tendsto hτ.le hboundary hstable hs
  have hb : ∀ᶠ a in l,
      0≤F.fullCoefficientAt a ∧ 0≤F.restCoefficientAt a ∧
        F.restCoefficientAt a≤alternatingShift (F.tuning a)/F.epsilon a ∧
          F.fullCoefficientAt a≤F.restCoefficientAt a := by
    filter_upwards [hconv,F.epsilon_pos,F.alternating_rate_lower hτ.le hboundary hstable,
      F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a hc he hm he1
    have hμ := sq_pos_of_pos he
    have hμL : F.epsilon a^2<1 := by nlinarith
    refine ⟨div_nonneg (sub_nonneg.mpr hc.1.le) he.le,
      div_nonneg (sub_nonneg.mpr hc.2.le) he.le,?_,?_⟩
    · exact div_le_div_of_nonneg_right (by linarith only [hm.2.1]) he.le
    · exact div_le_div_of_nonneg_right (sub_le_sub_left
        (Momentum.restRate_le_momentumRate (β:=(F.tuning a).beta)
          (τ:=(F.tuning a).tau) (F.tuning a).step_pos.ne' hμ hμL) 1) he.le
  refine ⟨hconv,?_,?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hshift
      (hb.mono fun _ h=>h.1) (hb.mono fun _ h=>h.2.2.2.trans h.2.2.1)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hshift
      (hb.mono fun _ h=>h.2.1) (hb.mono fun _ h=>h.2.2.1)

variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

/-- The literal real-epsilon statement of the source edge. -/
theorem zero_margin_coefficients_tendsto (he : F.epsilon=id)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    (hτ : 1/2<τ) (hboundary : y*(1+2*τ)=4)
    (hs : Tendsto F.stabilityMargin (𝓝[>] (0:ℝ)) (𝓝 (2*θ))) :
    (∀ᶠ ε in 𝓝[>] (0:ℝ),
      Momentum.momentumRate (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
        (F.tuning ε).step_pos.ne' (ε^2) 1<1 ∧
      Momentum.momentumRestRate (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
        (F.tuning ε).step_pos.ne' (ε^2) 1<1) ∧
      Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 0) ∧
        Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hst : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (F.epsilon ε^2) 1 := by
    simpa only [he,id_eq] using hstable
  have hf : F.fullCoefficientAt=F.fullCoefficient := by
    funext ε
    simp only [fullCoefficientAt,fullCoefficient,he,id_eq]
  have hr : F.restCoefficientAt=F.restCoefficient := by
    funext ε
    simp only [restCoefficientAt,restCoefficient,he,id_eq]
  have hh := F.zero_margin_filter hst hτ hboundary hs
  rw [hf,hr] at hh
  simpa only [he,id_eq] using hh

/-- The same zero constant in the literal condition number, for both actual rates. -/
theorem zero_margin_kappa_tendsto (he : F.epsilon=id)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    (hτ : 1/2<τ) (hboundary : y*(1+2*τ)=4)
    (hs : Tendsto F.stabilityMargin (𝓝[>] (0:ℝ)) (𝓝 (2*θ))) :
    Tendsto F.fullKappaCoefficient atTop (𝓝 0) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 0) := by
  have hh := F.zero_margin_coefficients_tendsto he hstable hτ hboundary hs
  exact ⟨F.full_kappa_transport hh.2.1,F.rest_kappa_transport hh.2.2⟩

end
end nesterov.TwoStep.Scaling
