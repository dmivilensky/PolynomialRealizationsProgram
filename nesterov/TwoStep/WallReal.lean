import nesterov.TwoStep.Wall
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! The wall theorem for arbitrary countably generated parameter filters.
In particular the parameter may be a real ε→0+ or a real κ→∞. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} [l.IsCountablyGenerated] [NeBot l]
  {ε : A→ℝ} {q : A→Momentum.Tuning} {c : ℝ}

omit [l.IsCountablyGenerated] [NeBot l] in
private theorem accelerated_tau_filter_bounded (hc : 0<c)
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ a in l,(q a).Stable (ε a^2) 1)
    (hrate : ∀ᶠ a in l,Quadratic.quadraticRate (ε a^2) 1
      (q a).beta (q a).tau (q a).stepSize≤1-c*ε a) :
    ∀ᶠ a in l,(q a).tau≤2/c^2 := by
  filter_upwards [he.eventually self_mem_nhdsWithin,hstable,hrate,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with a ha hs hr ha1
  exact (accelerated_tuning_bounds (q a) ha ha1 hc hs hr).2.2.1.le

omit [NeBot l] in
/-- The literal real-parameter wall theorem, also valid for any countably
generated parameter filter. Every sufficiently late member has an actual orbit. -/
theorem wall_of_limsup_filter (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ a in l,(q a).Stable (ε a^2) 1)
    (hrate : ∀ᶠ a in l,Quadratic.quadraticRate (ε a^2) 1
      (q a).beta (q a).tau (q a).stepSize≤1-c*ε a)
    (hlim : limsup (fun a=>(q a).tau) l<1/2) :
    ∀ᶠ a in l,∃ K : ℕ,6≤K ∧ HasPeriodicRestWitness (q a) (ε a^2) 1 K ∧
      1<Momentum.momentumRestRate (q a).beta (q a).tau (q a).stepSize
        (q a).step_pos.ne' (ε a^2) 1 := by
  obtain ⟨T,hTlim,hT⟩ := exists_between hlim
  have hb : IsBoundedUnder (·≤·) l (fun a=>(q a).tau) :=
    ⟨2/c^2,accelerated_tau_filter_bounded hc he hstable hrate⟩
  have ht : ∀ᶠ a in l,(q a).tau≤T :=
    (eventually_lt_of_limsup_lt hTlim hb).mono fun _ ha=>ha.le
  by_contra hn
  have hbad : ∃ᶠ a in l,¬∃ K : ℕ,6≤K ∧ HasPeriodicRestWitness (q a) (ε a^2) 1 K ∧
      1<Momentum.momentumRestRate (q a).beta (q a).tau (q a).stepSize
        (q a).step_pos.ne' (ε a^2) 1 := by simpa only [not_eventually] using hn
  obtain ⟨s,hs,hbs⟩ := exists_seq_forall_of_frequently hbad
  have hw := wall_periodic_rest hc (he.comp hs) (hs.eventually hstable) (hs.eventually hrate)
    hT (hs.eventually ht)
  obtain ⟨n,hn⟩ := hw.exists
  exact hbs n hn

/-- The literal liminf half-step rule for real parameter families. -/
theorem half_le_liminf_tau_filter (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ a in l,(q a).Stable (ε a^2) 1)
    (hrate : ∀ᶠ a in l,Quadratic.quadraticRate (ε a^2) 1
      (q a).beta (q a).tau (q a).stepSize≤1-c*ε a)
    (hrest : ∀ᶠ a in l,Momentum.momentumRestRate (q a).beta (q a).tau (q a).stepSize
      (q a).step_pos.ne' (ε a^2) 1≤1) :
    1/2≤liminf (fun a=>(q a).tau) l := by
  have hb : IsBoundedUnder (·≥·) l (fun a=>(q a).tau) := by
    refine ⟨0,?_⟩
    change ∀ᶠ a in l,0≤(q a).tau
    exact Eventually.of_forall fun a=>(q a).tau_nonneg
  have hco : IsCoboundedUnder (·≥·) l (fun a=>(q a).tau) :=
    isCoboundedUnder_ge_of_eventually_le l (accelerated_tau_filter_bounded hc he hstable hrate)
  apply (le_liminf_iff' hco hb).mpr
  intro T hT
  by_contra hn
  have hbad : ∃ᶠ a in l,(q a).tau<T := by simpa only [not_eventually,not_le] using hn
  obtain ⟨s,hs,hbs⟩ := exists_seq_forall_of_frequently hbad
  have hw := wall_restRate hc (he.comp hs) (hs.eventually hstable) (hs.eventually hrate)
    hT (Eventually.of_forall fun n=>(hbs n).le)
  obtain ⟨n,hn,hbound⟩ := (hw.and (hs.eventually hrest)).exists
  exact (not_lt_of_ge hbound) hn

end
end nesterov.TwoStep
