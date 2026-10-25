import polyak.General.Cubic
import polyak.General.Multipliers.Minimum

/-! Appendix D, Lemma near1.  Instead of an informal Taylor remainder, use
the exact radial difference quotient of the source cubic and compactness. -/

namespace polyak.General.Multipliers
noncomputable section
open Set Filter Topology

def radialQuotient (q : Tuning) (r c : ℝ) : ℝ :=
  c*(1+r+r^2+r^3+r^4) +
  (2*(q.y-1-q.beta)*c^2-(1+q.y-q.x))*(1+r+r^2+r^3) +
  (4*q.beta*c^3+(q.x*q.y-2*q.x-2*q.y+3+q.beta^2-
    q.beta*q.x-q.beta*q.y+2*q.beta)*c)*(1+r+r^2) +
  (2*(q.beta*q.x-3*q.beta-q.beta^2)*c^2-(1-q.x)*(1-q.y)+
    2*q.beta*q.y-q.beta^2)*(1+r) +
  (3*q.beta^2-q.beta*q.x-q.beta*q.y+2*q.beta)*c

theorem radial_identity (q : Tuning) (r c : ℝ) :
    q.H r c = (1-c)*q.L c + (1-r)*radialQuotient q r c := by
  unfold Tuning.H Tuning.L radialQuotient
  ring

theorem radial_one_one (q : Tuning) : radialQuotient q 1 1 = q.x*q.y := by
  unfold radialQuotient
  ring

theorem exists_positive_inner_band (q : Tuning)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 < q.L c) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ r c : ℝ,
      1-eta ≤ r → r < 1 → c ∈ Icc (-1 : ℝ) 1 → 0 < q.H r c := by
  have hlocal : ∀ c ∈ Icc (-1 : ℝ) 1,
      ∀ᶠ z : ℝ×ℝ in 𝓝 (1,c), z.1 < 1 → z.2 ∈ Icc (-1 : ℝ) 1 → 0 < q.H z.1 z.2 := by
    intro c hc
    by_cases hc1 : c = 1
    · subst c
      have hP : Continuous (fun z : ℝ×ℝ => radialQuotient q z.1 z.2) := by
        unfold radialQuotient; fun_prop
      have hQ : 0 < radialQuotient q 1 1 := by rw [radial_one_one]; exact mul_pos q.x_pos q.y_pos
      have hPn := (hP.continuousAt : ContinuousAt (fun z : ℝ×ℝ => radialQuotient q z.1 z.2) (1,1)).eventually (isOpen_Ioi.mem_nhds hQ)
      filter_upwards [hPn] with z hz hr hc
      rw [radial_identity]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hc.2) (hL z.2 hc).le)
        (mul_pos (sub_pos.mpr hr) hz)
    · have hH : 0 < q.H 1 c := by
        rw [q.H_one]
        exact mul_pos (sub_pos.mpr (lt_of_le_of_ne hc.2 hc1)) (hL c hc)
      have hcont : Continuous (fun z : ℝ×ℝ => q.H z.1 z.2) := by unfold Tuning.H; fun_prop
      filter_upwards [(hcont.continuousAt : ContinuousAt (fun z : ℝ×ℝ => q.H z.1 z.2) (1,c)).eventually (isOpen_Ioi.mem_nhds hH)] with z hz
      exact fun _ _ => hz
  have hu : ∀ᶠ r : ℝ in 𝓝 1, ∀ c ∈ Icc (-1 : ℝ) 1,
      r < 1 → c ∈ Icc (-1 : ℝ) 1 → 0 < q.H r c :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun r c => r < 1 → c ∈ Icc (-1 : ℝ) 1 → 0 < q.H r c) hlocal
  obtain ⟨d, hd, hdu⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨d/2, half_pos hd, ?_⟩
  intro r c hr hr1 hc
  have hrd : dist r 1 < d := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hr1.le)]
    linarith
  exact hdu hrd c hc hr1 hc

end
end polyak.General.Multipliers
