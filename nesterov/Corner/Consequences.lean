import nesterov.Corner.Rates
import nesterov.Corner.Regions

/-! The source's sufficient conditions for equality of the two corner bounds
and its explicit flow/alternating regions apply to the actual rates. -/
namespace nesterov.Corner
noncomputable section
open Set

def endpointConstant (θ a b : ℝ) : ℝ := min (Flow.cQ θ 2) (min (θ/3) (cpi θ a b))

theorem endpointConstant_pos {θ a b : ℝ} (hθ : 0<θ) (hmargin : θ<2*a+b) :
    0<endpointConstant θ a b :=
  lt_min (Flow.cQ_pos hθ (by norm_num))
    (lt_min (by positivity) (cpi_pos_iff.mpr hmargin))

theorem matched_minima_of_polynomial {θ a b : ℝ}
    (hpoly : ∀ ξ∈Icc (0:ℝ) 2,4*endpointConstant θ a b*(3-ξ)≤N θ a b ξ) :
    min (Flow.cQ θ 2) (cLag θ a b)=endpointConstant θ a b ∧
      min (Flow.cQ θ 2) (cDisc θ a b)=endpointConstant θ a b := by
  have hl : endpointConstant θ a b≤cLag θ a b := le_cLag_iff.mpr hpoly
  have hQ : endpointConstant θ a b≤Flow.cQ θ 2 := min_le_left _ _
  have hu : min (Flow.cQ θ 2) (cDisc θ a b)≤endpointConstant θ a b :=
    min_le_min_left _ (cDisc_endpoints θ a b)
  have horder := min_le_min_left (Flow.cQ θ 2) (cLag_le_cDisc θ a b)
  exact ⟨le_antisymm (horder.trans hu) (le_min hQ hl),
    le_antisymm hu (le_min hQ (hl.trans (cLag_le_cDisc θ a b)))⟩

end
end nesterov.Corner

namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

theorem corner_coefficients_of_polynomial [l.IsCountablyGenerated] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b)
    (hpoly : ∀ ξ∈Icc (0:ℝ) 2,
      4*Corner.endpointConstant θ a b*(3-ξ)≤Corner.N θ a b ξ) :
    Tendsto F.fullCoefficientAt l (𝓝 (Corner.endpointConstant θ a b)) ∧
      Tendsto F.restCoefficientAt l (𝓝 (Corner.endpointConstant θ a b)) := by
  have hm := Corner.matched_minima_of_polynomial hpoly
  have hp := Corner.endpointConstant_pos F.theta_pos hmargin
  have hLag : 0<Corner.cLag θ a b :=
    hp.trans_le (Corner.le_cLag_iff.mpr hpoly)
  have h := F.corner_coefficients_tendsto ha hb hmargin hLag (hm.1.trans hm.2.symm)
  rwa [hm.1] at h

theorem corner_coefficients_of_concave [l.IsCountablyGenerated] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hconc : 4*a+b≤2*θ) :
    Tendsto F.fullCoefficientAt l (𝓝 (Corner.endpointConstant θ a b)) ∧
      Tendsto F.restCoefficientAt l (𝓝 (Corner.endpointConstant θ a b)) := by
  apply F.corner_coefficients_of_polynomial ha hb hmargin
  intro ξ hξ
  exact Corner.concave_region_polynomial (c:=Corner.endpointConstant θ a b) hconc
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hξ

theorem corner_coefficients_of_discrete_min [l.IsCountablyGenerated] {a b ξ : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hLag : 0<Corner.cLag θ a b)
    (hξ : ξ∈Corner.discreteSet) (hmin : Corner.ratio θ a b ξ=Corner.cLag θ a b) :
    Tendsto F.fullCoefficientAt l (𝓝 (min (Flow.cQ θ 2) (Corner.cLag θ a b))) ∧
      Tendsto F.restCoefficientAt l (𝓝 (min (Flow.cQ θ 2) (Corner.cLag θ a b))) :=
  F.corner_coefficients_tendsto ha hb hmargin hLag
    (by rw [Corner.cLag_eq_cDisc_of_mem_min hξ hmin])

theorem corner_coefficients_of_quadratic [l.IsCountablyGenerated] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hQ : Flow.cQ θ 2≤Corner.cLag θ a b) :
    Tendsto F.fullCoefficientAt l (𝓝 (Flow.cQ θ 2)) ∧
      Tendsto F.restCoefficientAt l (𝓝 (Flow.cQ θ 2)) := by
  have hD : Flow.cQ θ 2≤Corner.cDisc θ a b := hQ.trans (Corner.cLag_le_cDisc _ _ _)
  have h := F.corner_coefficients_tendsto ha hb hmargin
    ((Flow.cQ_pos F.theta_pos (by norm_num)).trans_le hQ)
    (by rw [min_eq_left hQ,min_eq_left hD])
  rwa [min_eq_left hQ] at h

theorem corner_flow_region [l.IsCountablyGenerated] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hθ3 : θ≤3) (ha' : a≤5*θ/12) (hb' : 7*θ/6≤2*a+b) :
    Tendsto F.fullCoefficientAt l (𝓝 (θ/3)) ∧
      Tendsto F.restCoefficientAt l (𝓝 (θ/3)) := by
  have hm := Corner.flow_region_minimum F.theta_pos.le hθ3 ha' hb'
  have hLag : 0<Corner.cLag θ a b := by
    rw [(Corner.flow_region_minima ha' hb').1]
    exact div_pos F.theta_pos (by norm_num)
  have h := F.corner_coefficients_tendsto ha hb (by linarith [F.theta_pos]) hLag
    (hm.1.trans hm.2.symm)
  rwa [hm.1] at h

theorem corner_alternating_region [l.IsCountablyGenerated] {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hθ3 : θ≤3) (hb' : 2*a+b<7*θ/6)
    (hab : 5*a+2*b≤11*θ/4) :
    Tendsto F.fullCoefficientAt l (𝓝 (Corner.cpi θ a b)) ∧
      Tendsto F.restCoefficientAt l (𝓝 (Corner.cpi θ a b)) := by
  have hm := Corner.alternating_region_minimum F.theta_pos.le hθ3 hb' hab
  have hLag : 0<Corner.cLag θ a b := by
    rw [(Corner.alternating_region_minima hb' hab).1]
    exact Corner.cpi_pos_iff.mpr hmargin
  have h := F.corner_coefficients_tendsto ha hb hmargin hLag (hm.1.trans hm.2.symm)
  rwa [hm.1] at h

end
end nesterov.TwoStep.Scaling
