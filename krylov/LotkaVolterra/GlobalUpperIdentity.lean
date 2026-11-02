import krylov.LotkaVolterra.GlobalLowerIdentity
import krylov.LotkaVolterra.GlobalChordUniqueness

/-!
Article: `main_krylov`, `apC:prop:LV`, uniqueness of the full separating graph.
The actual bounded chord is unique near the saddle. In upper logarithmic
coordinates, ordinary global Lipschitz uniqueness continues that identity
through the entire upper branch. Together with the lower-branch identity,
this proves uniqueness on the full positive state axis.

Source: scalar bounded expansion at the saddle and Picard uniqueness.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

theorem upperLogisticRate_eq_exponential {γ t v : ℝ} (hγ₁ : γ < 1)
    (hv : 1 - v ≠ 0) :
    logisticSlopeRate γ false (logisticParameter t) v =
      -saddleSlopeRate γ (-(saddleU γ * Real.exp (-t))) v := by
  have hB := saddleU_pos hγ₁
  have hE := Real.exp_pos t
  have hEn := Real.exp_pos (-t)
  have hU : 0 < saddleU γ * (1 + Real.exp (-t)) := by positivity
  have hh := upperLogisticRate_eq (γ := γ) (v := v)
    (ne_of_gt hB) (ne_of_gt hU) hv
  have hq : (saddleU γ * (1 + Real.exp (-t)) - saddleU γ) /
      (saddleU γ * (1 + Real.exp (-t))) = logisticParameter t := by
    unfold logisticParameter
    rw [Real.exp_neg]
    field_simp
    ring
  have hz : saddleU γ - saddleU γ * (1 + Real.exp (-t)) =
      -(saddleU γ * Real.exp (-t)) := by ring
  simpa only [hq, hz] using hh

namespace SubcriticalGraph
variable {γ : ℝ} (G : SubcriticalGraph γ)

def upperLogisticSlope (t : ℝ) : ℝ := G.rawChord (-(2 * Real.exp (-t)))

theorem upperLogisticSlope_bounds (hγ₁ : γ < 1) (t : ℝ) :
    G.upperLogisticSlope t ∈ Ioo 0 γ := by
  exact G.rawChord_bounds_of_lt_two hγ₁ (by linarith [Real.exp_pos (-t)])
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) (ne_of_gt (Real.exp_pos _))))

theorem upperLogisticSlope_hasDerivAt (hγ₁ : γ < 1) (t : ℝ) :
    HasDerivAt G.upperLogisticSlope
      (logisticSlopeRate γ false (logisticParameter t) (G.upperLogisticSlope t)) t := by
  have hu : -(2 * Real.exp (-t)) < 2 := by linarith [Real.exp_pos (-t)]
  have hu₀ : -(2 * Real.exp (-t)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (by norm_num) (ne_of_gt (Real.exp_pos _)))
  have hv := G.upperLogisticSlope_bounds hγ₁ t
  have hd : HasDerivAt (fun t : ℝ ↦ -(2 * Real.exp (-t))) (2 * Real.exp (-t)) t := by
    convert (((hasDerivAt_id t).neg.exp.const_mul 2).neg) using 1
    · rfl
    · simp only [Pi.neg_apply, id_eq]
      ring
  have hh := (G.rawChord_hasDerivAt_of_lt_two hγ₁ hu hu₀).comp t hd
  have harg : (saddleU γ / 2) * -(2 * Real.exp (-t)) =
      -(saddleU γ * Real.exp (-t)) := by ring
  rw [harg] at hh
  change HasDerivAt G.upperLogisticSlope
    (saddleSlopeRate γ (-(saddleU γ * Real.exp (-t))) (G.upperLogisticSlope t) /
      -(2 * Real.exp (-t)) * (2 * Real.exp (-t))) t at hh
  have hid : saddleSlopeRate γ (-(saddleU γ * Real.exp (-t))) (G.upperLogisticSlope t) /
      -(2 * Real.exp (-t)) * (2 * Real.exp (-t)) =
      -saddleSlopeRate γ (-(saddleU γ * Real.exp (-t))) (G.upperLogisticSlope t) := by
    field_simp
  rw [hid, ← upperLogisticRate_eq_exponential hγ₁ (by linarith [hv.2])] at hh
  exact hh

theorem unique_upper_logisticSlope (hγ : 0 < γ) (hγ₁ : γ < 1)
    (G' : SubcriticalGraph γ) : G.upperLogisticSlope = G'.upperLogisticSlope := by
  have hsame : G.rawChord (-1) = G'.rawChord (-1) := by
    apply bounded_saddle_chord_unique hγ hγ₁
      (fun u hu h₀ ↦ let hh := G.rawChord_bounds hγ₁ hu h₀; ⟨hh.1.le, hh.2.le⟩)
      (fun u hu h₀ ↦ let hh := G'.rawChord_bounds hγ₁ hu h₀; ⟨hh.1.le, hh.2.le⟩)
      (fun _ hu h₀ ↦ G.rawChord_hasDerivAt hγ₁ hu h₀)
      (fun _ hu h₀ ↦ G'.rawChord_hasDerivAt hγ₁ hu h₀)
      (-1) (by norm_num) (by norm_num)
  have hinit : G.upperLogisticSlope (Real.log 2) = G'.upperLogisticSlope (Real.log 2) := by
    have hE : -(2 * Real.exp (-Real.log 2)) = (-1 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    simpa only [upperLogisticSlope, hE] using hsame
  obtain ⟨_, K, _, hLip⟩ := clippedLogisticSlopeRate_bounds hγ hγ₁ false
  apply ODE_solution_unique_univ (v := clippedLogisticSlopeRate γ false)
    (s := fun _ ↦ univ) (K := K) (t₀ := Real.log 2)
    (fun t ↦ (hLip t).lipschitzOnWith)
    (fun t ↦ ⟨?_, mem_univ _⟩) (fun t ↦ ⟨?_, mem_univ _⟩) hinit
  · have hv := G.upperLogisticSlope_bounds hγ₁ t
    simpa only [clippedLogisticSlopeRate, saddleSlopeClip_eq ⟨hv.1.le, hv.2.le⟩]
      using G.upperLogisticSlope_hasDerivAt hγ₁ t
  · have hv := G'.upperLogisticSlope_bounds hγ₁ t
    simpa only [clippedLogisticSlopeRate, saddleSlopeClip_eq ⟨hv.1.le, hv.2.le⟩]
      using G'.upperLogisticSlope_hasDerivAt hγ₁ t

theorem unique_upper_graph (hγ : 0 < γ) (hγ₁ : γ < 1) (G' : SubcriticalGraph γ) :
    EqOn G.σ G'.σ (Ioi (saddleU γ)) := by
  intro U hU
  change saddleU γ < U at hU
  have hB := saddleU_pos hγ₁
  have hd := sub_pos.mpr hU
  have hE : Real.exp (-upperGraphTime γ U) = (U - saddleU γ) / saddleU γ := by
    unfold upperGraphTime
    rw [Real.exp_neg, Real.exp_log (div_pos hB hd)]
    field_simp
  have hden : (saddleU γ / 2) * -(2 * Real.exp (-upperGraphTime γ U)) = saddleU γ - U := by
    rw [hE]
    field_simp
    ring
  have hback : saddleU γ - (saddleU γ / 2) * -(2 * Real.exp (-upperGraphTime γ U)) = U := by
    rw [hden]
    ring
  have hh := congrFun (G.unique_upper_logisticSlope hγ hγ₁ G') (upperGraphTime γ U)
  change (saddleS γ - G.σ (saddleU γ - (saddleU γ / 2) *
    -(2 * Real.exp (-upperGraphTime γ U)))) /
      ((saddleU γ / 2) * -(2 * Real.exp (-upperGraphTime γ U))) =
    (saddleS γ - G'.σ (saddleU γ - (saddleU γ / 2) *
    -(2 * Real.exp (-upperGraphTime γ U)))) /
      ((saddleU γ / 2) * -(2 * Real.exp (-upperGraphTime γ U))) at hh
  rw [hback, hden] at hh
  have hm := (div_left_inj' (sub_ne_zero.mpr (ne_of_lt hU))).mp hh
  linarith

/-- The constructed separating graph is unique on its full mathematical domain. -/
theorem unique (hγ : 0 < γ) (hγ₁ : γ < 1) (G' : SubcriticalGraph γ) :
    EqOn G.σ G'.σ (Ioi (0 : ℝ)) := by
  intro U hU
  rcases lt_trichotomy U (saddleU γ) with h | h | h
  · exact G.unique_lower_graph hγ hγ₁ G' ⟨hU, h⟩
  · rw [h, G.saddle, G'.saddle]
  · exact G.unique_upper_graph hγ hγ₁ G' h

end SubcriticalGraph
end
end krylov.LotkaVolterra
