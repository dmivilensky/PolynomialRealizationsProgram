import krylov.LotkaVolterra.GlobalEndpointUniqueness
import krylov.LotkaVolterra.AnalyticGraphField

/-!
Article: main_krylov, apC:prop:g1 and the analytic extension preceding apC:eq:f.
Use: extend the constructed endpoint graph slightly to the left of U=1.
The auxiliary bounded ODE clips time only below U=1/2. Its solution agrees
with the original shooting graph for U≥1 by actual ODE uniqueness, and its
clipping is inactive near every physical graph point, including U=1.
Source: Picard--Lindelöf, Grönwall and the analytic Picard construction.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology NNReal

private def endpointConstantRate (e : ℝ) : ℝ :=
  (endpointGapClip e - 3) / (endpointGapClip e + 1)

private theorem endpointConstantRate_lipschitz :
    LipschitzWith 1 endpointConstantRate := by
  have hLip : LipschitzOnWith 1 (fun e : ℝ ↦ (e - 3) / (e + 1)) (Icc 1 3) := by
    apply (convex_Icc (1 : ℝ) 3).lipschitzOnWith_of_nnnorm_deriv_le
    · intro e he
      exact (((hasDerivAt_id e).sub_const 3).div
        ((hasDerivAt_id e).add_const 1) (by simpa only [id_eq] using (show e + 1 ≠ 0 by linarith [he.1]))).differentiableAt
    · intro e he
      have hd : HasDerivAt (fun e : ℝ ↦ (e - 3) / (e + 1))
          ((1 * (e + 1) - (e - 3) * 1) / (e + 1) ^ 2) e := by
        convert! ((hasDerivAt_id e).sub_const 3).div
          ((hasDerivAt_id e).add_const 1) (by simpa only [id_eq] using
            (show e + 1 ≠ 0 by linarith [he.1])) using 1
      rw [hd.deriv]
      change |((1 : ℝ) * (e + 1) - (e - 3) * 1) / (e + 1) ^ 2| ≤ 1
      have hp : 0 < (e + 1) ^ 2 := sq_pos_of_pos (by linarith [he.1])
      rw [abs_of_nonneg (div_nonneg (by ring_nf; norm_num) hp.le)]
      apply (div_le_iff₀ hp).mpr
      nlinarith [he.1]
  rw [lipschitzWith_iff_dist_le_mul]
  intro e f
  calc
    dist (endpointConstantRate e) (endpointConstantRate f) ≤
        1 * dist (endpointGapClip e) (endpointGapClip f) :=
      hLip.dist_le_mul _ (endpointGapClip_mem e) _ (endpointGapClip_mem f)
    _ ≤ 1 * dist e f := by simpa using lipschitz_endpointGapClip.dist_le_mul e f

private theorem endpointConstantRate_norm (e : ℝ) : ‖endpointConstantRate e‖ ≤ 1 := by
  have h := endpointGapClip_mem e
  change |(endpointGapClip e - 3) / (endpointGapClip e + 1)| ≤ 1
  rw [abs_div, abs_of_nonpos (by linarith [h.2]), abs_of_pos (by linarith [h.1])]
  apply (div_le_iff₀ (by linarith [h.1] : 0 < endpointGapClip e + 1)).mpr
  linarith [h.1]

/-- Bounded extension which preserves the rational endpoint equation for
U>1/2 whenever the gap is in the physical strip. -/
def extendedEndpointRate (U e : ℝ) : ℝ :=
  2 * clippedEndpointGraphRate (2 * U) e - endpointConstantRate e

theorem extendedEndpointRate_lipschitz (U : ℝ) :
    LipschitzWith 7 (extendedEndpointRate U) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro e f
  calc
    dist (extendedEndpointRate U e) (extendedEndpointRate U f) ≤
        ‖2 * (clippedEndpointGraphRate (2 * U) e - clippedEndpointGraphRate (2 * U) f)‖ +
          ‖endpointConstantRate e - endpointConstantRate f‖ := by
      rw [dist_eq_norm]
      convert norm_sub_le
        (2 * (clippedEndpointGraphRate (2 * U) e - clippedEndpointGraphRate (2 * U) f))
        (endpointConstantRate e - endpointConstantRate f) using 1
      congr 1
      unfold extendedEndpointRate
      ring
    _ ≤ 7 * dist e f := by
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hA := (clippedEndpointGraphRate_lipschitz (2 * U)).dist_le_mul e f
      have hB := endpointConstantRate_lipschitz.dist_le_mul e f
      simp only [dist_eq_norm, NNReal.coe_ofNat, NNReal.coe_one, one_mul] at hA hB
      rw [dist_eq_norm]
      linarith

theorem extendedEndpointRate_continuous_time (e : ℝ) :
    Continuous (extendedEndpointRate · e) := by
  exact (continuous_const.mul
    ((clippedEndpointGraphRate_continuous_time e).comp
      (continuous_const.mul continuous_id))).sub continuous_const

theorem extendedEndpointRate_norm_le (U e : ℝ) :
    ‖extendedEndpointRate U e‖ ≤ 13 := by
  calc
    ‖extendedEndpointRate U e‖ ≤
        ‖2 * clippedEndpointGraphRate (2 * U) e‖ + ‖endpointConstantRate e‖ := norm_sub_le _ _
    _ ≤ 13 := by
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [clippedEndpointGraphRate_norm_le (2 * U) e, endpointConstantRate_norm e]

theorem extendedEndpointRate_eq {U e : ℝ} (hU : 1 / 2 ≤ U)
    (he : e ∈ Icc (1 : ℝ) 3) :
    extendedEndpointRate U e = endpointGraphRate U e := by
  rw [extendedEndpointRate, clippedEndpointGraphRate_eq (by linarith) he]
  simp only [endpointConstantRate, endpointGapClip_eq he, endpointGraphRate]
  have hU₀ : U ≠ 0 := by linarith
  field_simp
  ring

/-- The endpoint graph is the restriction of an analytic graph on an open
interval containing the entire physical half-line, including its initial point. -/
theorem exists_analytic_endpoint_graph :
    ∃ σ : ℝ → ℝ, ∃ ε > 0,
      (∀ U > 1 - ε, AnalyticAt ℝ σ U ∧ 0 < σ U ∧ 0 < σ U + 1 - U ∧
        HasDerivAt σ (2 * σ U * (σ U - 1 - U) / (U * (σ U + 1 - U))) U) ∧
      (∀ U ≥ 1, U + 1 < σ U ∧ σ U < U + 3 ∧ σ U ≤ 4 * U) := by
  obtain ⟨e, he⟩ := exists_global_endpoint_graph_gap
  obtain ⟨g, hg₁, hg⟩ := exists_global_solution_at_of_bounded_lipschitz
    (L := 13) (K := 7) extendedEndpointRate_lipschitz
    extendedEndpointRate_continuous_time extendedEndpointRate_norm_le 1 (e 1)
  have hge : EqOn g e (Ici 1) := by
    intro U hU
    apply ODE_solution_unique_of_mem_Icc_right
      (v := extendedEndpointRate) (s := fun _ ↦ univ)
      (fun t _ ↦ (extendedEndpointRate_lipschitz t).lipschitzOnWith)
      (HasDerivAt.continuousOn fun t _ ↦ hg t)
      (fun t _ ↦ (hg t).hasDerivWithinAt) (fun _ _ ↦ mem_univ _)
      (HasDerivAt.continuousOn fun t ht ↦ (he t ht.1).2)
      (fun t ht ↦ ?_) (fun _ _ ↦ mem_univ _) hg₁ ⟨hU, le_rfl⟩
    rw [extendedEndpointRate_eq (by linarith [ht.1]) (he t ht.1).1]
    exact (he t ht.1).2.hasDerivWithinAt
  have hg₁strict : g 1 ∈ Ioo (1 : ℝ) 3 := by
    rw [hg₁]
    exact endpoint_graph_gap_strict he le_rfl
  have hnear : ∀ᶠ U in 𝓝 (1 : ℝ), 1 / 2 < U ∧ g U ∈ Ioo (1 : ℝ) 3 :=
    Filter.Eventually.and
      (show ∀ᶠ U : ℝ in 𝓝 1, 1 / 2 < U from
        isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi (1 / 2) by norm_num))
      ((hg 1).continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hg₁strict))
  obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε := min (δ / 2) (1 / 4)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hstrip (U : ℝ) (hU : 1 - ε < U) :
      1 / 2 < U ∧ g U ∈ Ioo (1 : ℝ) 3 := by
    by_cases hU₁ : 1 ≤ U
    · rw [hge hU₁]
      exact ⟨by linarith, endpoint_graph_gap_strict he hU₁⟩
    · apply hδp
      rw [Real.dist_eq, abs_lt]
      dsimp [ε] at hU
      constructor <;> linarith [min_le_left (δ / 2) (1 / 4)]
  let σ : ℝ → ℝ := fun U ↦ U + g U
  have hd (U : ℝ) (hU : 1 - ε < U) : HasDerivAt σ
      (2 * σ U * (σ U - 1 - U) / (U * (σ U + 1 - U))) U := by
    have hs := hstrip U hU
    have hrate : 2 * σ U * (σ U - 1 - U) / (U * (σ U + 1 - U)) =
        1 + extendedEndpointRate U (g U) := by
      rw [extendedEndpointRate_eq hs.1.le ⟨hs.2.1.le, hs.2.2.le⟩,
        endpointGraphRate_eq (by linarith [hs.1]) (by linarith [hs.2.1])]
      dsimp [σ]
      have hid : U + g U + 1 - U = g U + 1 := by ring
      rw [hid]
      have hU₀ : U ≠ 0 := by linarith [hs.1]
      have hg₀ : g U + 1 ≠ 0 := by linarith [hs.2.1]
      field_simp
      ring
    rw [hrate]
    exact (hasDerivAt_id U).add (hg U)
  refine ⟨σ, ε, hε, ?_, ?_⟩
  · intro U hU
    have hs := hstrip U hU
    have hpos : 0 < σ U := by dsimp [σ]; linarith [hs.1, hs.2.1]
    have hden : 0 < σ U + 1 - U := by dsimp [σ]; linarith [hs.2.1]
    refine ⟨analyticAt_graph_solution (γ := 1) (by linarith [hs.1]) (ne_of_gt hden) ?_,
      hpos, hden, ?_⟩
    · filter_upwards [isOpen_Ioi.mem_nhds hU] with V hV
      simpa using hd V hV
    · simpa using hd U hU
  · intro U hU
    have hs := endpoint_graph_gap_strict he hU
    dsimp [σ]
    rw [hge hU]
    exact ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hs.2]⟩

end
end krylov.LotkaVolterra
