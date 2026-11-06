import nesterov.TwoStep.FrontierOptimization
import nesterov.TwoStep.FrontierSequences

/-! Frontier(iv): domination concerns the literal two rate limsups, even if
those rate coefficients do not converge. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

private theorem rest_limsup_ceiling [l.IsCountablyGenerated]
    (hs : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    limsup (fun a=>(F.restCoefficientAt a:EReal)) l≤(Flow.cF θ y:EReal) := by
  by_contra hh
  obtain ⟨b,hb,hlim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  have hbound : ∀ᶠ a in l,(F.restCoefficientAt a:EReal)≤(b:EReal) := by
    filter_upwards [F.rest_coefficient_eventually_le_filter hs (EReal.coe_lt_coe_iff.mp hb)] with a ha
    exact EReal.coe_le_coe_iff.mpr ha
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) hbound)) hlim

private theorem quadratic_limsup_ceiling :
    limsup (fun a=>((1-F.rate a)/F.epsilon a:EReal)) l≤(Flow.cQ θ y:EReal) := by
  by_contra hh
  obtain ⟨b,hb,hlim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  have hbound : ∀ᶠ a in l,((1-F.rate a)/F.epsilon a:EReal)≤(b:EReal) := by
    filter_upwards [F.quadratic_coefficient_eventually_lt (EReal.coe_lt_coe_iff.mp hb)] with a ha
    exact EReal.coe_le_coe_iff.mpr ha.le
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) hbound)) hlim

/-- The complete componentwise domination statement for actual rate constants. -/
theorem frontier_limsup_pair [NeBot l] [l.IsCountablyGenerated]
    (hs : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) (hτ : 1/2≤τ) :
    ∃ θ' : ℝ,2*Real.sqrt (frontierStep τ)≤θ' ∧ θ'≤3*Real.sqrt (frontierStep τ/2) ∧
      limsup (fun a=>((1-F.rate a)/F.epsilon a:EReal)) l≤(Flow.cQ θ' (frontierStep τ):EReal) ∧
      limsup (fun a=>(F.restCoefficientAt a:EReal)) l≤((θ'/3:ℝ):EReal) ∧
        Flow.cF θ' (frontierStep τ)=θ'/3 := by
  obtain ⟨θ',hl,hu,hq,hf,he⟩ := frontier_pair_domination F.theta_pos F.step_pos
    (by linarith : 0≤τ) (F.stability_margin_le hs)
  exact ⟨θ',hl,hu,F.quadratic_limsup_ceiling.trans (EReal.coe_le_coe_iff.mpr hq),
    (F.rest_limsup_ceiling hs).trans (EReal.coe_le_coe_iff.mpr hf),he⟩

end
end nesterov.TwoStep.Scaling
