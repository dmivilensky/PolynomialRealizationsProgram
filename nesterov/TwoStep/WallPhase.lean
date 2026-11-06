import nesterov.TwoStep.WallReal

/-! The wall's phase inequality, periodic orbit and strict growth use the same
integer period, for arbitrary countably generated parameter filters. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} [l.IsCountablyGenerated]
  {ε : A → ℝ} {q : A → Momentum.Tuning} {c : ℝ}

theorem wall_negative_polynomial_filter (hc : 0<c)
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ a in l, (q a).Stable (ε a^2) 1)
    (hrate : ∀ᶠ a in l, Quadratic.quadraticRate (ε a^2) 1
      (q a).beta (q a).tau (q a).stepSize ≤ 1-c*ε a)
    (hlim : limsup (fun a => (q a).tau) l < 1/2) :
    ∀ᶠ a in l, ∃ K : ℕ, 6≤K ∧
      Ltau (q a).beta (q a).tau ((q a).stepSize*ε a^2) (q a).stepSize
        (1-Real.cos (2*Real.pi/K)) < 0 := by
  obtain ⟨T,hTlim,hT⟩ := exists_between hlim
  have hb : IsBoundedUnder (·≤·) l (fun a => (q a).tau) := by
    refine ⟨2/c^2, ?_⟩
    change ∀ᶠ a in l, (q a).tau≤2/c^2
    filter_upwards [he.eventually self_mem_nhdsWithin,hstable,hrate,
      (he.mono_right nhdsWithin_le_nhds).eventually
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a ha hs hr ha1
    exact (accelerated_tuning_bounds (q a) ha ha1 hc hs hr).2.2.1.le
  have ht : ∀ᶠ a in l, (q a).tau≤T :=
    (eventually_lt_of_limsup_lt hTlim hb).mono fun _ ha => ha.le
  by_contra hn
  have hbad : ∃ᶠ a in l, ¬∃ K : ℕ, 6≤K ∧
      Ltau (q a).beta (q a).tau ((q a).stepSize*ε a^2) (q a).stepSize
        (1-Real.cos (2*Real.pi/K)) < 0 := by
    simpa only [not_eventually] using hn
  obtain ⟨s,hs,hbs⟩ := exists_seq_forall_of_frequently hbad
  have hw := wall_negative_polynomial hc (he.comp hs) (hs.eventually hstable)
    (hs.eventually hrate) hT (hs.eventually ht)
  obtain ⟨n,hn⟩ := hw.exists
  exact hbs n hn

theorem wall_phase_periodic_rest_filter (hc : 0<c)
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ a in l, (q a).Stable (ε a^2) 1)
    (hrate : ∀ᶠ a in l, Quadratic.quadraticRate (ε a^2) 1
      (q a).beta (q a).tau (q a).stepSize ≤ 1-c*ε a)
    (hlim : limsup (fun a => (q a).tau) l < 1/2) :
    ∀ᶠ a in l, ∃ K : ℕ, 6≤K ∧
      Phase.momentumAngle (q a) (ε a^2) 1 (2*Real.pi/K) < Real.pi/K ∧
      HasPeriodicRestWitness (q a) (ε a^2) 1 K ∧
      1 < Momentum.momentumRestRate (q a).beta (q a).tau (q a).stepSize
        (q a).step_pos.ne' (ε a^2) 1 := by
  filter_upwards [wall_negative_polynomial_filter hc he hstable hrate hlim,hstable,
    he.eventually self_mem_nhdsWithin,
    (he.mono_right nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a ha hs ha0 ha1
  obtain ⟨K,hK,hneg⟩ := ha
  have hμ : 0<ε a^2 := sq_pos_of_pos ha0
  have hμL : ε a^2<1 := by nlinarith
  have hneg' : Ltau (q a).beta (q a).tau ((q a).stepSize*ε a^2)
      ((q a).stepSize*1) (1-Real.cos (2*Real.pi/K))<0 := by
    simpa only [mul_one] using hneg
  have hangle : 2*Real.pi/K ∈ Ioo (0:ℝ) Real.pi := by
    simpa [polyak.General.Regions.rationalAngle] using
      polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
  have hp := (stable_Ltau_phase_sign (q a) hμ hμL hs
    ⟨hangle.1,hangle.2.le⟩).2.2.mp hneg'
  rw [show 2*Real.pi/(K:ℝ)/2=Real.pi/K by ring] at hp
  exact ⟨K,hK,hp,negative_Ltau_periodic_rest (q a) hμ hμL hs (by omega) hneg',
    negative_Ltau_restRate (q a) hμ hμL hs (by omega) hneg'⟩

end
end nesterov.TwoStep
