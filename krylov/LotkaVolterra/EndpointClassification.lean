import krylov.LotkaVolterra.EndpointClassificationField

/-!
Article: `main_krylov`, `apC:prop:g1`, classification of endpoint shooting.
For the normalized gap the exact secant has expansion rate at least `1/U`.
Thus two solutions bounded in `[0,3]` cannot differ: their squared distance
divided by `U²` is nondecreasing. Order preservation then identifies the
strict lower and upper exit sets as the two intervals separated by the
constructed shooting value. Source: scalar ODE uniqueness and mean value.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

theorem endpointRatioRate_sub {U q p : ℝ} (hU : U ≠ 0)
    (hq : U * q + 1 ≠ 0) (hp : U * p + 1 ≠ 0) :
    endpointRatioRate U q - endpointRatioRate U p =
      (q - p) * (1 / U + 4 * (U - 1) / (U * ((U * q + 1) * (U * p + 1)))) := by
  unfold endpointRatioRate
  field_simp
  ring

theorem endpointRatioRate_expansion {U q p : ℝ} (hU : 1 ≤ U)
    (hq : 0 ≤ q) (hp : 0 ≤ p) :
    (q - p) ^ 2 / U ≤ (q - p) * (endpointRatioRate U q - endpointRatioRate U p) := by
  have hUp : 0 < U := by linarith
  have hqp : 0 < U * q + 1 := by nlinarith
  have hpp : 0 < U * p + 1 := by nlinarith
  rw [endpointRatioRate_sub (ne_of_gt hUp) (ne_of_gt hqp) (ne_of_gt hpp)]
  have hh : 0 ≤ 4 * (U - 1) / (U * ((U * q + 1) * (U * p + 1))) :=
    div_nonneg (by linarith) (by positivity)
  simp only [div_eq_mul_inv] at *
  nlinarith [mul_nonneg (sq_nonneg (q - p)) hh]

theorem bounded_endpoint_ratio_unique {q p : ℝ → ℝ}
    (hq : ∀ U ≥ 1, q U ∈ Icc (0 : ℝ) 4 ∧ HasDerivAt q (endpointRatioRate U (q U)) U)
    (hp : ∀ U ≥ 1, p U ∈ Icc (0 : ℝ) 4 ∧ HasDerivAt p (endpointRatioRate U (p U)) U) :
    q 1 = p 1 := by
  let D : ℝ → ℝ := fun U ↦ (q U - p U) ^ 2 / U ^ 2
  have hd (U : ℝ) (hU : 1 ≤ U) : HasDerivAt D
      ((2 * (q U - p U) * (endpointRatioRate U (q U) - endpointRatioRate U (p U)) * U ^ 2 -
        (q U - p U) ^ 2 * (2 * U)) / (U ^ 2) ^ 2) U := by
    convert (((hq U hU).2.sub (hp U hU).2).pow 2).div ((hasDerivAt_id U).pow 2)
      (by nlinarith : U ^ 2 ≠ 0) using 1
    · rfl
    · dsimp
      ring
  have hmono : MonotoneOn D (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (HasDerivAt.continuousOn fun U hU ↦ hd U hU)
      (fun U hU ↦ (hd U (interior_subset hU)).differentiableAt.differentiableWithinAt)
    intro U hU
    have hU₁ : 1 ≤ U := interior_subset hU
    rw [(hd U hU₁).deriv]
    apply div_nonneg ?_ (sq_nonneg _)
    have hh := endpointRatioRate_expansion hU₁ (hq U hU₁).1.1 (hp U hU₁).1.1
    have hUp : 0 < U := by linarith
    have hh' := (div_le_iff₀ hUp).mp hh
    nlinarith [mul_nonneg hUp.le (show 0 ≤
      (q U - p U) * (endpointRatioRate U (q U) - endpointRatioRate U (p U)) * U -
        (q U - p U) ^ 2 by linarith)]
  by_contra hne
  let d := q 1 - p 1
  have hd₀ : 0 < |d| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let V : ℝ := 1 + 5 / |d|
  have hV : 1 ≤ V := by
    dsimp [V]
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) hd₀.le)
  have hVp : 0 < V := by linarith
  have hh : d ^ 2 ≤ (q V - p V) ^ 2 / V ^ 2 := by
    simpa only [D, one_pow, div_one] using hmono (a := (1 : ℝ)) (b := V) (show (1 : ℝ) ≤ 1 from le_rfl) hV hV
  have hscaled : d ^ 2 * V ^ 2 ≤ (q V - p V) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hVp)).mp hh
  have hb : (q V - p V) ^ 2 ≤ 16 := by
    have hqV := (hq V hV).1
    have hpV := (hp V hV).1
    nlinarith [mul_nonneg (show 0 ≤ 4 - (q V - p V) by linarith [hqV.2, hpV.1])
      (show 0 ≤ 4 + (q V - p V) by linarith [hqV.1, hpV.2])]
  have hid : |d| * V = |d| + 5 := by dsimp [V]; field_simp
  have hh₄ : 5 ≤ |d| * V := by linarith
  have hsq : 25 ≤ (|d| * V) ^ 2 := by nlinarith
  rw [mul_pow, sq_abs] at hsq
  linarith

theorem endpointRatioFlow_strictMono {U : ℝ} (hU : 1 ≤ U) :
    StrictMono (fun ξ ↦ endpointRatioFlow ξ U) := by
  intro ξ η hξη
  have hneq (V : ℝ) : endpointRatioFlow ξ V ≠ endpointRatioFlow η V := by
    intro he
    have hfun := ODE_solution_unique_univ (v := clippedEndpointRatioRate)
      (s := fun _ ↦ univ) (t₀ := V)
      (fun U ↦ (clippedEndpointRatioRate_lipschitz U).lipschitzOnWith)
      (fun U ↦ ⟨endpointRatioFlow_hasDerivAt ξ U, mem_univ _⟩)
      (fun U ↦ ⟨endpointRatioFlow_hasDerivAt η U, mem_univ _⟩) he
    have hi := congrFun hfun 1
    rw [endpointRatioFlow_initial, endpointRatioFlow_initial] at hi
    linarith
  by_contra! hn
  have hC : Continuous (fun U ↦ endpointRatioFlow η U - endpointRatioFlow ξ U) :=
    (continuous_iff_continuousAt.mpr fun U ↦ (endpointRatioFlow_hasDerivAt η U).continuousAt).sub
      (continuous_iff_continuousAt.mpr fun U ↦ (endpointRatioFlow_hasDerivAt ξ U).continuousAt)
  obtain ⟨V, _, he⟩ := intermediate_value_Icc' hU hC.continuousOn
    (show (0 : ℝ) ∈ Icc (endpointRatioFlow η U - endpointRatioFlow ξ U)
      (endpointRatioFlow η 1 - endpointRatioFlow ξ 1) by
      rw [endpointRatioFlow_initial, endpointRatioFlow_initial]
      constructor <;> linarith)
  exact hneq V (by linarith)

/-- The normalized constructed separating graph solves precisely the
bounded shooting equation on its full positive-state domain. -/
theorem endpoint_graph_normalized_solution {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    ∀ U ≥ 1, e U / U ∈ Icc (0 : ℝ) 3 ∧
      HasDerivAt (fun U ↦ e U / U) (endpointRatioRate U (e U / U)) U := by
  intro U hU
  have hUp : 0 < U := by linarith
  have heU := (he U hU).1
  refine ⟨⟨div_nonneg (by linarith [heU.1]) hUp.le, ?_⟩, ?_⟩
  · apply (div_le_iff₀ hUp).mpr
    linarith [heU.2]
  · have hh := (he U hU).2.div (hasDerivAt_id U) (ne_of_gt hUp)
    convert hh using 1
    · rfl
    · rw [endpointGraphRate_eq (ne_of_gt hUp) (by linarith [heU.1])]
      unfold endpointRatioRate
      dsimp
      field_simp [ne_of_gt hUp, show e U + 1 ≠ 0 by linarith [heU.1]]
      ring

/-- The clipped shooting flow is exactly the constructed separating graph
on every finite positive-state interval. -/
theorem endpointRatioFlow_matches_gap {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U)
    {U : ℝ} (hU : 1 ≤ U) : endpointRatioFlow (e 1) U = e U / U := by
  have hp (V : ℝ) (hV : 1 ≤ V) : HasDerivAt (fun V ↦ e V / V)
      (clippedEndpointRatioRate V (e V / V)) V := by
    rw [clippedEndpointRatioRate_eq hV ⟨(endpoint_graph_normalized_solution he V hV).1.1,
      (endpoint_graph_normalized_solution he V hV).1.2.trans (by norm_num)⟩]
    exact (endpoint_graph_normalized_solution he V hV).2
  have hh := ODE_solution_unique_of_mem_Icc_right (v := clippedEndpointRatioRate)
    (s := fun _ ↦ univ) (K := 23) (a := 1) (b := U)
    (fun V _ ↦ (clippedEndpointRatioRate_lipschitz V).lipschitzOnWith)
    (HasDerivAt.continuousOn fun V _ ↦ endpointRatioFlow_hasDerivAt (e 1) V)
    (fun V _ ↦ (endpointRatioFlow_hasDerivAt (e 1) V).hasDerivWithinAt)
    (fun _ _ ↦ mem_univ _)
    (HasDerivAt.continuousOn fun V hV ↦ hp V hV.1)
    (fun V hV ↦ (hp V hV.1).hasDerivWithinAt) (fun _ _ ↦ mem_univ _)
    (show endpointRatioFlow (e 1) 1 = e 1 / 1 by rw [endpointRatioFlow_initial, div_one])
  exact hh ⟨hU, le_rfl⟩

theorem endpointRatioFlow_nonescape_iff {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U)
    {ξ : ℝ} : (∀ U ≥ 1, endpointRatioFlow ξ U ∈ Icc (0 : ℝ) 3) ↔ ξ = e 1 := by
  constructor
  · intro hstrip
    have hq (U : ℝ) (hU : 1 ≤ U) : endpointRatioFlow ξ U ∈ Icc (0 : ℝ) 3 ∧
        HasDerivAt (endpointRatioFlow ξ) (endpointRatioRate U (endpointRatioFlow ξ U)) U := by
      refine ⟨hstrip U hU, ?_⟩
      simpa only [clippedEndpointRatioRate_eq hU
        ⟨(hstrip U hU).1, (hstrip U hU).2.trans (by norm_num)⟩] using endpointRatioFlow_hasDerivAt ξ U
    have hh := bounded_endpoint_ratio_unique
      (fun U hU ↦ ⟨⟨(hq U hU).1.1, (hq U hU).1.2.trans (by norm_num)⟩, (hq U hU).2⟩)
      (fun U hU ↦ ⟨⟨(endpoint_graph_normalized_solution he U hU).1.1,
        (endpoint_graph_normalized_solution he U hU).1.2.trans (by norm_num)⟩,
          (endpoint_graph_normalized_solution he U hU).2⟩)
    simpa only [endpointRatioFlow_initial, div_one] using hh
  · rintro rfl U hU
    rw [endpointRatioFlow_matches_gap he hU]
    exact (endpoint_graph_normalized_solution he U hU).1

/-- Lower finite shooting exit, written with the original initial `s`. -/
def endpointLowerShootingSet : Set ℝ :=
  {s | 2 < s ∧ ∃ U ≥ 1, endpointRatioFlow (s - 1) U < 1 / U}

/-- Upper finite shooting exit, which is exactly entrance into `P₁`. -/
def endpointUpperShootingSet : Set ℝ :=
  {s | 2 < s ∧ ∃ U ≥ 1, 3 < endpointRatioFlow (s - 1) U}

theorem endpoint_shooting_sets_intervals {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    endpointLowerShootingSet = Ioo (2 : ℝ) (1 + e 1) ∧
      endpointUpperShootingSet = Ioi (1 + e 1) := by
  have he₁ := endpoint_graph_gap_strict he (show (1 : ℝ) ≤ 1 from le_rfl)
  have hc (U : ℝ) (hU : 1 ≤ U) : 1 / U < endpointRatioFlow (e 1) U ∧
      endpointRatioFlow (e 1) U ≤ 3 := by
    rw [endpointRatioFlow_matches_gap he hU]
    have hUp : 0 < U := by linarith
    exact ⟨(div_lt_div_iff_of_pos_right hUp).mpr (endpoint_graph_gap_strict he hU).1,
      (endpoint_graph_normalized_solution he U hU).1.2⟩
  constructor
  · ext s
    constructor
    · rintro ⟨hs, U, hU, hlow⟩
      refine ⟨hs, ?_⟩
      by_contra! hn
      have hh : endpointRatioFlow (e 1) U ≤ endpointRatioFlow (s - 1) U :=
        (endpointRatioFlow_strictMono hU).monotone (by linarith)
      linarith [(hc U hU).1]
    · rintro ⟨hs, hscrit⟩
      refine ⟨hs, ?_⟩
      by_contra! hn
      have hstrip (U : ℝ) (hU : 1 ≤ U) : endpointRatioFlow (s - 1) U ∈ Icc (0 : ℝ) 3 := by
        have hm := endpointRatioFlow_strictMono hU (show s - 1 < e 1 by linarith)
        have hpos : 0 < 1 / U := one_div_pos.mpr (by linarith)
        exact ⟨hpos.le.trans (hn U hU), hm.le.trans (hc U hU).2⟩
      have heq := (endpointRatioFlow_nonescape_iff he).mp hstrip
      linarith
  · ext s
    constructor
    · rintro ⟨_, U, hU, hhi⟩
      by_contra! hn
      change ¬1 + e 1 < s at hn
      have hh : endpointRatioFlow (s - 1) U ≤ endpointRatioFlow (e 1) U :=
        (endpointRatioFlow_strictMono hU).monotone (by linarith)
      linarith [(hc U hU).2]
    · intro hscrit
      change 1 + e 1 < s at hscrit
      refine ⟨by linarith [he₁.1], ?_⟩
      by_contra! hn
      have hstrip (U : ℝ) (hU : 1 ≤ U) : endpointRatioFlow (s - 1) U ∈ Icc (0 : ℝ) 3 := by
        have hm := endpointRatioFlow_strictMono hU (show e 1 < s - 1 by linarith)
        have hpos : 0 < 1 / U := one_div_pos.mpr (by linarith)
        exact ⟨hpos.le.trans ((hc U hU).1.le.trans hm.le), hn U hU⟩
      have heq := (endpointRatioFlow_nonescape_iff he).mp hstrip
      change 1 + e 1 < s at hscrit
      linarith

/-- Both endpoint shooting classes are open, disjoint, and nonempty, and
there is exactly one remaining initial value. -/
theorem endpoint_shooting_classification {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    IsOpen endpointLowerShootingSet ∧ IsOpen endpointUpperShootingSet ∧
      Disjoint endpointLowerShootingSet endpointUpperShootingSet ∧
      endpointLowerShootingSet.Nonempty ∧ endpointUpperShootingSet.Nonempty ∧
      Ioi (2 : ℝ) \ (endpointLowerShootingSet ∪ endpointUpperShootingSet) = {1 + e 1} := by
  obtain ⟨hlo, hhi⟩ := endpoint_shooting_sets_intervals he
  have he₁ := endpoint_graph_gap_strict he (show (1 : ℝ) ≤ 1 from le_rfl)
  rw [hlo, hhi]
  refine ⟨isOpen_Ioo, isOpen_Ioi, ?_, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr fun _ hs ht ↦ (not_lt_of_ge hs.2.le) ht
  · exact nonempty_Ioo.mpr (by linarith [he₁.1])
  · exact nonempty_Ioi
  · ext s
    simp only [mem_sdiff, mem_Ioi, mem_union, mem_Ioo, mem_singleton_iff]
    constructor
    · rintro ⟨hs, hn⟩
      by_contra! heq
      rcases lt_or_gt_of_ne heq with hh | hh
      · exact hn (Or.inl ⟨hs, hh⟩)
      · exact hn (Or.inr hh)
    · rintro rfl
      exact ⟨by linarith [he₁.1], by simp⟩

end
end krylov.LotkaVolterra
