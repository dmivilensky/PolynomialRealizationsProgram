import krylov.LotkaVolterra.EndpointOrbitSides

/-!
Article: `main_krylov`, `apC:prop:g1`, complete original-orbit classification.
The bounded normalized shooting witnesses are stopped before clipping can
change the field, then traversed in finite actual LV time. Thus the open
interval classification concerns the article's original trajectories.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

private theorem lower_endpoint_graph_segment {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U)
    {ξ : ℝ} (hξ : 1 < ξ) (hcrit : ξ < e 1) :
    ∃ V > 1, endpointRatioFlow ξ V = 0 ∧ ∀ U ∈ Icc (1 : ℝ) V,
      0 ≤ endpointRatioFlow ξ U ∧
        HasDerivAt (endpointRatioFlow ξ) (endpointRatioRate U (endpointRatioFlow ξ U)) U := by
  let q := endpointRatioFlow ξ
  have hqhi (U : ℝ) (hU : 1 ≤ U) : q U ≤ 3 := by
    have hh := endpointRatioFlow_strictMono hU hcrit
    dsimp only at hh
    rw [endpointRatioFlow_matches_gap he hU] at hh
    exact hh.le.trans (endpoint_graph_normalized_solution he U hU).1.2
  have hex : ∃ U ≥ 1, q U ≤ 0 := by
    by_contra! hn
    have hh := (endpointRatioFlow_nonescape_iff he).mp
      (fun U hU ↦ ⟨(hn U hU).le, hqhi U hU⟩)
    linarith
  have hqC : Continuous q := continuous_iff_continuousAt.mpr
    fun U ↦ (endpointRatioFlow_hasDerivAt ξ U).continuousAt
  obtain ⟨R, hR, hqR, hbefore⟩ := exists_first_zero_of_nonpositive
    (w := fun t ↦ q (1 + t)) (hqC.comp (continuous_const.add continuous_id))
    (by dsimp [q]; rw [add_zero, endpointRatioFlow_initial]; linarith)
    (by obtain ⟨U, hU, hlast⟩ := hex; exact ⟨U - 1, by linarith, by simpa using hlast⟩)
  let V := 1 + R
  have hV : 1 < V := by dsimp [V]; linarith
  refine ⟨V, hV, hqR, fun U hU ↦ ?_⟩
  have hqlo : 0 ≤ q U := by
    rcases lt_or_eq_of_le hU.2 with hh | hh
    · have ht : U - 1 ∈ Ico (0 : ℝ) R := ⟨by linarith [hU.1], by dsimp [V] at hh; linarith⟩
      simpa using (hbefore (U - 1) ht).le
    · simpa only [hh, V, hqR] using (le_refl (0 : ℝ))
  refine ⟨hqlo, ?_⟩
  have hqr : q U ∈ Icc (0 : ℝ) 4 := ⟨hqlo, (hqhi U hU.1).trans (by norm_num)⟩
  have hd := endpointRatioFlow_hasDerivAt ξ U
  change HasDerivAt q (clippedEndpointRatioRate U (q U)) U at hd
  rwa [clippedEndpointRatioRate_eq hU.1 hqr] at hd

private theorem upper_endpoint_graph_segment {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U)
    {ξ : ℝ} (hcrit : e 1 < ξ) (hξ : ξ ≤ 3) :
    ∃ V > 1, endpointRatioFlow ξ V = 7 / 2 ∧ ∀ U ∈ Icc (1 : ℝ) V,
      0 ≤ endpointRatioFlow ξ U ∧
        HasDerivAt (endpointRatioFlow ξ) (endpointRatioRate U (endpointRatioFlow ξ U)) U := by
  let q := endpointRatioFlow ξ
  have hqlo (U : ℝ) (hU : 1 ≤ U) : 0 ≤ q U := by
    have hh := endpointRatioFlow_strictMono hU hcrit
    dsimp only at hh
    rw [endpointRatioFlow_matches_gap he hU] at hh
    exact (endpoint_graph_normalized_solution he U hU).1.1.trans hh.le
  have hex : ∃ U ≥ 1, 7 / 2 ≤ q U := by
    by_contra! hn
    have hqr (U : ℝ) (hU : 1 ≤ U) : q U ∈ Icc (0 : ℝ) 4 :=
      ⟨hqlo U hU, by linarith [hn U hU]⟩
    have hqd (U : ℝ) (hU : 1 ≤ U) : q U ∈ Icc (0 : ℝ) 4 ∧
        HasDerivAt q (endpointRatioRate U (q U)) U := by
      refine ⟨hqr U hU, ?_⟩
      have hd := endpointRatioFlow_hasDerivAt ξ U
      change HasDerivAt q (clippedEndpointRatioRate U (q U)) U at hd
      rwa [clippedEndpointRatioRate_eq hU (hqr U hU)] at hd
    have hh := bounded_endpoint_ratio_unique hqd
      (fun U hU ↦ ⟨⟨(endpoint_graph_normalized_solution he U hU).1.1,
        (endpoint_graph_normalized_solution he U hU).1.2.trans (by norm_num)⟩,
          (endpoint_graph_normalized_solution he U hU).2⟩)
    dsimp [q] at hh
    rw [endpointRatioFlow_initial, div_one] at hh
    linarith
  have hqC : Continuous q := continuous_iff_continuousAt.mpr
    fun U ↦ (endpointRatioFlow_hasDerivAt ξ U).continuousAt
  obtain ⟨R, hR, hqR, hbefore⟩ := exists_first_zero_of_nonpositive
    (w := fun t ↦ 7 / 2 - q (1 + t))
    (continuous_const.sub (hqC.comp (continuous_const.add continuous_id)))
    (by dsimp [q]; rw [add_zero, endpointRatioFlow_initial]; linarith)
    (by obtain ⟨U, hU, hlast⟩ := hex
        refine ⟨U - 1, by linarith, ?_⟩
        simpa using sub_nonpos.mpr hlast)
  let V := 1 + R
  have hV : 1 < V := by dsimp [V]; linarith
  have hqV : q V = 7 / 2 := by dsimp [V]; linarith
  refine ⟨V, hV, hqV, fun U hU ↦ ⟨hqlo U hU.1, ?_⟩⟩
  have hqhi : q U ≤ 4 := by
    rcases lt_or_eq_of_le hU.2 with hh | hh
    · have ht : U - 1 ∈ Ico (0 : ℝ) R := ⟨by linarith [hU.1], by dsimp [V] at hh; linarith⟩
      have hlast := hbefore (U - 1) ht
      have hid : 1 + (U - 1) = U := by ring
      rw [hid] at hlast
      linarith
    · rw [hh, hqV]
      norm_num
  have hd := endpointRatioFlow_hasDerivAt ξ U
  change HasDerivAt q (clippedEndpointRatioRate U (q U)) U at hd
  rwa [clippedEndpointRatioRate_eq hU.1 ⟨hqlo U hU.1, hqhi⟩] at hd

/-- Every original initial value below the separator has an actual finite
orbit leaving `E`. -/
theorem endpointLowerOrbitSet_superset {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    Ioo (2 : ℝ) (1 + e 1) ⊆ endpointLowerOrbitSet := by
  intro s hs
  obtain ⟨V, hV, hqV, hq⟩ := lower_endpoint_graph_segment he
    (show 1 < s - 1 by linarith [hs.1]) (show s - 1 < e 1 by linarith [hs.2])
  obtain ⟨α, hα₀, T, hT, hα, hp, hlast⟩ := endpoint_finite_graph_traversal hV hq
  have hinit : α 0 = (s, 1) := by
    rw [endpointRatioFlow_initial] at hα₀
    simpa using hα₀
  refine ⟨hs.1, α, hinit, T, hT.le, hα, fun t ht ↦ (hp t ht).1, ?_⟩
  rw [hlast, hqV]
  norm_num

/-- Every original initial value above the separator has an actual finite
orbit entering `P₁`, including initial points already inside that wedge. -/
theorem endpointUpperOrbitSet_superset {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    Ioi (1 + e 1) ⊆ endpointUpperOrbitSet := by
  intro s hs
  have he₁ := endpoint_graph_gap_strict he (show (1 : ℝ) ≤ 1 from le_rfl)
  have hs₂ : 2 < s := by change 1 + e 1 < s at hs; linarith [he₁.1]
  by_cases hs₄ : 4 < s
  · obtain ⟨α, hα₀, ε, hε, hα⟩ := exists_local_solution 1 0 (s, 1)
    have hαd := hα 0 (show (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) by constructor <;> linarith)
    refine ⟨hs₂, α, hα₀, 0, le_rfl, ?_, ?_, ?_⟩
    · intro t ht
      have ht₀ : t = 0 := le_antisymm ht.2 ht.1
      simpa only [ht₀] using hαd
    · intro t ht
      have ht₀ : t = 0 := le_antisymm ht.2 ht.1
      rw [ht₀, hα₀]
      exact ⟨by linarith, by norm_num⟩
    · rw [hα₀]
      exact ⟨hs₄, by norm_num, by linarith⟩
  · obtain ⟨V, hV, hqV, hq⟩ := upper_endpoint_graph_segment he
      (show e 1 < s - 1 by change 1 + e 1 < s at hs; linarith) (show s - 1 ≤ 3 by linarith)
    obtain ⟨α, hα₀, T, hT, hα, hp, hlast⟩ := endpoint_finite_graph_traversal hV hq
    have hinit : α 0 = (s, 1) := by
      rw [endpointRatioFlow_initial] at hα₀
      simpa using hα₀
    refine ⟨hs₂, α, hinit, T, hT.le, hα, fun t ht ↦ (hp t ht).1, ?_⟩
    rw [hlast, hqV]
    change 4 < V * (1 + 7 / 2) ∧ 0 < V ∧ V < V * (1 + 7 / 2) / 4
    constructor
    · linarith
    · constructor <;> linarith

/-- Complete classification of the actual endpoint orbit classes from the
article, proved through finite original LV trajectories. -/
theorem endpoint_actual_orbit_sets_intervals {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    endpointLowerOrbitSet = Ioo (2 : ℝ) (1 + e 1) ∧
      endpointUpperOrbitSet = Ioi (1 + e 1) :=
  ⟨Subset.antisymm (endpointLowerOrbitSet_subset he) (endpointLowerOrbitSet_superset he),
    Subset.antisymm (endpointUpperOrbitSet_subset he) (endpointUpperOrbitSet_superset he)⟩

theorem endpoint_actual_shooting_sets_agree {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    endpointLowerOrbitSet = endpointLowerShootingSet ∧
      endpointUpperOrbitSet = endpointUpperShootingSet := by
  obtain ⟨hlo, hhi⟩ := endpoint_actual_orbit_sets_intervals he
  obtain ⟨hlo', hhi'⟩ := endpoint_shooting_sets_intervals he
  exact ⟨hlo.trans hlo'.symm, hhi.trans hhi'.symm⟩

/-- All topological assertions in the endpoint proposition, now for the
actual original-orbit classes rather than auxiliary shooting coordinates. -/
theorem endpoint_actual_orbit_classification {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    IsOpen endpointLowerOrbitSet ∧ IsOpen endpointUpperOrbitSet ∧
      Disjoint endpointLowerOrbitSet endpointUpperOrbitSet ∧
      endpointLowerOrbitSet.Nonempty ∧ endpointUpperOrbitSet.Nonempty ∧
      Ioi (2 : ℝ) \ (endpointLowerOrbitSet ∪ endpointUpperOrbitSet) = {1 + e 1} := by
  obtain ⟨hlo, hhi⟩ := endpoint_actual_shooting_sets_agree he
  rw [hlo, hhi]
  exact endpoint_shooting_classification he

end
end krylov.LotkaVolterra
