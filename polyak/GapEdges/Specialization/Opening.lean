import polyak.GapEdges.Specialization.Curvature
import polyak.Levels.Geometry.Convexity

/-! The sign of the actual edge slope determines the side of the dip.
At slope zero the entire dip is empty, not merely locally absent. -/
noncomputable section
namespace polyak.GapEdges
open General Levels ModeLocking Set Filter
open scoped Topology

theorem firstEdgePhase_local (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    firstEdgePhase q k =ᶠ[𝓝 (2 * Real.pi / k)]
      Geometry.shiftedAngle q (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) := by
  have hω := Chart.boundaryAngle_strict_mem hk
  change 2 * Real.pi / (k : ℝ) ∈ Ioo 0 Real.pi at hω
  filter_upwards [Ioo_mem_nhds hω.1 hω.2] with x hx
  exact Geometry.jointAngle_actual q _ ⟨hx.1.le, hx.2.le⟩

theorem first_gap_hasDerivAt (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    HasDerivAt (fun x => Geometry.shiftedAngle q
      (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) x - x / 2)
      (firstChi q k) (2 * Real.pi / k) := by
  have hh := (Geometry.hasDerivAt_shiftedAngle q
    (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) (Chart.boundaryAngle_strict_mem hk)).sub
      ((hasDerivAt_id (2 * Real.pi / (k : ℝ))).div_const 2)
  have hd := (firstEdgePhase_local q hk).deriv_eq
  have he := (Geometry.hasDerivAt_shiftedAngle q
    (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) (Chart.boundaryAngle_strict_mem hk)).deriv
  simp only [Chart.boundaryAngle] at he hh
  convert hh using 1
  · funext x
    rfl
  · simp only [firstChi, hd, he]

theorem first_dip_direction (q : Tuning) {k : ℕ} (hk : 3 ≤ k) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) Real.pi)
    (hdip : Geometry.shiftedAngle q (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) x < x / 2) :
    (2 * Real.pi / (k : ℝ) < x ∧ firstChi q k < 0) ∨
      (x < 2 * Real.pi / (k : ℝ) ∧ 0 < firstChi q k) := by
  let s := FareyPlateau.Edge.shift q k (2 * Real.pi / k)
  let f := fun y => Geometry.shiftedAngle q s y - y / 2
  let ω := 2 * Real.pi / (k : ℝ)
  have hf := Geometry.phase_line_strictConvexOn q s 1 0
  simp only [one_mul, mul_zero, sub_zero] at hf
  change StrictConvexOn ℝ (Geometry.phaseBelow q s) f at hf
  have hω := Chart.boundaryAngle_strict_mem hk
  change 2 * Real.pi / (k : ℝ) ∈ Ioo 0 Real.pi at hω
  have hphase := FareyPlateau.Edge.phase_at_shift q hk hω
  have hzero : f ω = 0 := by dsimp [f, ω, s]; rw [hphase]; ring
  have hωin : ω ∈ Geometry.phaseBelow q s := by
    refine ⟨hω, ?_⟩
    rw [hphase]
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by exact_mod_cast (show 2 ≤ k by omega))
  have hxin : x ∈ Geometry.phaseBelow q s :=
    ⟨hx, hdip.le.trans (div_le_div_of_nonneg_right hx.2.le (by norm_num))⟩
  have hneg : f x < 0 := sub_neg.mpr hdip
  have hneq : x ≠ ω := by intro he; rw [he, hzero] at hneg; exact (lt_irrefl 0) hneg
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · right
    have hh := hf.slope_lt_of_hasDerivAt hxin hωin hlt (first_gap_hasDerivAt q hk)
    rw [slope_def_field, hzero] at hh
    have hs : 0 < (0 - f x) / (ω - x) := div_pos (by linarith) (sub_pos.mpr hlt)
    exact ⟨hlt, hs.trans hh⟩
  · left
    have hh := hf.lt_slope_of_hasDerivAt hωin hxin hgt (first_gap_hasDerivAt q hk)
    rw [slope_def_field, hzero, sub_zero] at hh
    exact ⟨hgt, hh.trans (div_neg_of_neg_of_pos hneg (sub_pos.mpr hgt))⟩

theorem first_dip_empty_iff (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    Geometry.dipReal q (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) = ∅ ↔ firstChi q k = 0 := by
  constructor
  · intro hempty
    have hm : IsLocalMin (fun x => Geometry.shiftedAngle q
        (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) x - x / 2) (2 * Real.pi / k) := by
      have hω := Chart.boundaryAngle_strict_mem hk
      change 2 * Real.pi / (k : ℝ) ∈ Ioo 0 Real.pi at hω
      filter_upwards [Ioo_mem_nhds hω.1 hω.2] with x hx
      have hn : ¬Geometry.shiftedAngle q (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) x < x / 2 := by
        intro h
        have hh : x ∈ Geometry.dipReal q (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) :=
          ⟨⟨hx.1.le, hx.2.le⟩, h⟩
        simp only [hempty, mem_empty_iff_false] at hh
      have hp := FareyPlateau.Edge.phase_at_shift q hk hω
      rw [hp, show Real.pi / (k : ℝ) - (2 * Real.pi / k) / 2 = 0 by ring]
      exact sub_nonneg.mpr (le_of_not_gt hn)
    exact hm.hasDerivAt_eq_zero (first_gap_hasDerivAt q hk)
  · intro hzero
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    change x ∈ Icc (0 : ℝ) Real.pi ∧ Geometry.shiftedAngle q (FareyPlateau.Edge.shift q k (2 * Real.pi / k)) x < x / 2 at hx
    have hω : x ∈ Ioo (0 : ℝ) Real.pi := by
      constructor
      · by_contra hn
        have he : x = 0 := le_antisymm (le_of_not_gt hn) hx.1.1
        have hbad := hx.2
        rw [he, Geometry.shiftedAngle_zero, zero_div] at hbad
        linarith [Real.pi_pos]
      · by_contra hn
        have he : x = Real.pi := le_antisymm hx.1.2 (le_of_not_gt hn)
        have hbad := hx.2
        rw [he, Geometry.shiftedAngle_pi] at hbad
        linarith [Real.pi_pos]
    rcases first_dip_direction q hk hω hx.2 with ⟨_, hn⟩ | ⟨_, hp⟩ <;> rw [hzero] at * <;> linarith

end polyak.GapEdges
