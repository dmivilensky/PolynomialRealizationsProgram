import nesterov.Faithful.LeadingOrder
import nesterov.Faithful.Necessary

/-! The source's negative-leading-term and necessary local-symbol conclusions. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

theorem negative_leading_rate {p : ℕ} {s : ℝ}
    (hterm : HasLeadingEvenTerm (F.u 0) F.q0 p s) (hs : s<0) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),1<Rates.rate (F.method ε) (ε^2) 1 := by
  by_cases hneg : effectiveLead (F.u 0) F.q0 y<0
  · obtain ⟨_,_,_,_,he⟩ := negative_lead_divergence F hneg
    exact he.mono fun _ h=>h.2.1
  by_cases hhalf : effectiveLead (F.u 0) F.q0 y=1/2
  · obtain ⟨K,_,hK⟩ := family_half_negative F hhalf hterm hs
    exact ((hK K le_rfl).2).mono fun _ h=>h.choose_spec.2.2.1
  have hp : p=2 := (leading_order_two_iff F.step_pos (F.u_one 0) F.q0_one hterm).mpr hhalf
  have hr := leading_even_ratio hterm
  rw [hp] at hr
  have hq := (symbol_quartic_ratio (F.u 0) F.q0 F.step_pos (F.u_one 0) F.q0_one).mono_left
    (nhdsGT_le_nhdsNE (0:ℝ))
  have hcoeff : s=(2*effectiveLead (F.u 0) F.q0 y-1)/(2*y) := tendsto_nhds_unique hr hq
  have hτ : effectiveLead (F.u 0) F.q0 y<1/2 := by
    rw [hcoeff] at hs
    have hh := (div_lt_iff₀ (by linarith [F.step_pos] : 0<2*y)).mp hs
    linarith
  have habs : |effectiveLead (F.u 0) F.q0 y|<1/2 := by
    rw [abs_of_nonneg (le_of_not_gt hneg)]
    exact hτ
  obtain ⟨K,_,hK⟩ := family_below_half F habs
  exact ((hK K le_rfl).2).mono fun _ h=>h.choose_spec.2.2.1

/-- Stable families necessarily have a nonnegative symbol near zero; the
question of its sign at arbitrary finite frequencies remains separate. -/
theorem stable_symbol_eventually_nonnegative
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.rate (F.method ε) (ε^2) 1≤1) :
    ∀ᶠ ω in 𝓝[>] (0:ℝ),0≤limitSymbol (F.u 0) F.q0 ω := by
  by_cases hz : ∀ ω : ℝ,limitSymbol (F.u 0) F.q0 ω=0
  · exact Eventually.of_forall (fun ω=>by rw [hz])
  have hn : ∃ ω : ℝ,limitSymbol (F.u 0) F.q0 ω≠0 := by push Not at hz;exact hz
  obtain ⟨p,_,s,hterm⟩ := exists_leading_even_term (F.u 0) F.q0 F.step_pos (F.u_one 0) F.q0_one hn
  have hnonneg : 0≤s := by
    by_contra hn
    obtain ⟨ε,he⟩ := ((negative_leading_rate F hterm (lt_of_not_ge hn)).and hs).exists
    exact not_lt_of_ge he.2 he.1
  have hspos : 0<s := lt_of_le_of_ne hnonneg (Ne.symm hterm.1)
  have hratio := (leading_even_ratio hterm).eventually (eventually_gt_nhds hspos)
  filter_upwards [hratio,self_mem_nhdsWithin] with ω hω hω0
  have hh := (lt_div_iff₀ (pow_pos hω0 (2*p))).mp hω
  simpa only [zero_mul] using hh.le

end
end nesterov.Faithful
