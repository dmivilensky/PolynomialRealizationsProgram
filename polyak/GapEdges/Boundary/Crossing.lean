import polyak.GapEdges.Boundary.Diagonal
import polyak.GapEdges.Boundary.EveryRay

/-! The actual divergence boundary is nonempty in every gap.  Near every
interior point of the diagonal side, its projection meets every ray. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set

theorem boundary_every_gap {K : ℕ} (hK : 2 ≤ K) :
    IsOpen (positiveGap K) ∧ IsOpen (negativeGap K) ∧
      (positiveGap K).Nonempty ∧ (negativeGap K).Nonempty ∧
      (ModeLocking.BoundaryInGap K).Nonempty :=
  ⟨positiveGap_isOpen K, negativeGap_isOpen K, positiveGap_nonempty hK,
    negativeGap_nonempty hK,
    boundaryInGap_nonempty_of_signs hK (positiveGap_nonempty hK) (negativeGap_nonempty hK)⟩

def rayTuning {K : ℕ} (hK : 2 ≤ K) {r₁ r₂ : ℝ}
    (hl : Chart.boundaryCosine K < r₁) (hr : r₁ < r₂)
    (hu : r₂ < Chart.boundaryCosine (K + 1))
    (a : Ioi (Chart.amplitudeFloor r₁ r₂)) : Chart.GapTunings K :=
  Chart.gapInverse hK ⟨(a.val, r₁, r₂), hl, hr, hu, a.property⟩

theorem continuous_rayTuning {K : ℕ} (hK : 2 ≤ K) {r₁ r₂ : ℝ}
    (hl : Chart.boundaryCosine K < r₁) (hr : r₁ < r₂)
    (hu : r₂ < Chart.boundaryCosine (K + 1)) : Continuous (rayTuning hK hl hr hu) := by
  apply (Chart.gapHomeomorph hK).symm.continuous.comp
  apply Continuous.subtype_mk
  exact continuous_subtype_val.prodMk continuous_const

theorem ray_meets_boundary_of_positive {K : ℕ} (hK : 2 ≤ K) {r₁ r₂ a : ℝ}
    (hl : Chart.boundaryCosine K < r₁) (hr : r₁ < r₂)
    (hu : r₂ < Chart.boundaryCosine (K + 1))
    (ha : Chart.amplitudeFloor r₁ r₂ < a)
    (hpos : 0 < Threshold.sigma (rayTuning hK hl hr hu ⟨a, ha⟩).val) :
    ∃ b : ℝ, ∃ q : Tuning, q ∈ ModeLocking.BoundaryInGap K ∧
      Chart.coefficients q = Chart.gapPolynomial b r₁ r₂ := by
  let : ConnectedSpace (Ioi (Chart.amplitudeFloor r₁ r₂)) :=
    isConnected_iff_connectedSpace.mp isConnected_Ioi
  obtain ⟨A, hA, hneg⟩ := every_ray_eventually_negative hK hl hr hu
  let b : Ioi (Chart.amplitudeFloor r₁ r₂) := ⟨A + 1, by change Chart.amplitudeFloor r₁ r₂ < A + 1; linarith⟩
  have hb := (hneg (A + 1) (by linarith) (rayTuning hK hl hr hu b).val
    (Chart.coefficients_inverseTuning _)).2
  have hc : Continuous (fun c : Ioi (Chart.amplitudeFloor r₁ r₂) =>
      Threshold.sigma (rayTuning hK hl hr hu c).val) :=
    Global.Threshold.continuous_sigma.comp
      (continuous_subtype_val.comp (continuous_rayTuning hK hl hr hu))
  obtain ⟨c, hz⟩ := intermediate_value_univ b ⟨a, ha⟩ hc ⟨hb.le, hpos.le⟩
  refine ⟨c.val, (rayTuning hK hl hr hu c).val, ?_, Chart.coefficients_inverseTuning _⟩
  rw [boundaryInGap_eq_zero]
  exact ⟨(rayTuning hK hl hr hu c).property, hz⟩

theorem diagonal_projection_neighborhood {K : ℕ} (hK : 2 ≤ K) {r : ℝ}
    (hl : Chart.boundaryCosine K < r) (hu : r < Chart.boundaryCosine (K + 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r₁ r₂ : ℝ,
      Chart.boundaryCosine K < r₁ → r₁ < r₂ → r₂ < Chart.boundaryCosine (K + 1) →
      |r₁ - r| < δ → |r₂ - r| < δ →
      ∃ b : ℝ, ∃ q : Tuning, q ∈ ModeLocking.BoundaryInGap K ∧
        Chart.coefficients q = Chart.gapPolynomial b r₁ r₂ := by
  let a := Chart.amplitudeFloor r r + 1
  have ha : Chart.amplitudeFloor r r < a := by dsimp [a]; linarith
  let U := {x : ℝ × ℝ | (a, x.1, x.2) ∈ positiveRootSet}
  have hU : IsOpen U := positiveRootSet_isOpen.preimage
    (continuous_const.prodMk continuous_id)
  have hm : (r, r) ∈ U := diagonal_mem_positiveRootSet hK hl hu ha
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU (r, r) hm
  refine ⟨δ, hδ, ?_⟩
  intro r₁ r₂ h₁ hr h₂ he₁ he₂
  have hx : (a, r₁, r₂) ∈ positiveRootSet := hball (show (r₁, r₂) ∈ Metric.ball (r, r) δ from by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro he₁ he₂)
  have hxsave := hx
  obtain ⟨C, hC, heC⟩ := hx
  have hfloor : Chart.amplitudeFloor r₁ r₂ < a := by
    have hu₁ := hr.trans (h₂.trans (Chart.boundaryCosine_succ_lt_one hK))
    have hu₂ := h₂.trans (Chart.boundaryCosine_succ_lt_one hK)
    have hh := C.property.2.1
    rw [heC, Chart.gapPolynomial_one] at hh
    exact (div_lt_iff₀ (mul_pos (sub_pos.mpr hu₁) (sub_pos.mpr hu₂))).mpr (by linarith)
  apply ray_meets_boundary_of_positive hK h₁ hr h₂ hfloor
  apply positive_of_mem_positiveRootSet hxsave
  exact Chart.coefficients_inverseTuning _

end polyak.GapEdges
