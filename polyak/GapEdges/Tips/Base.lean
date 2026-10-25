import polyak.FareyPlateau.Edge.Jets
import polyak.ModeLocking.TwoLag.Extension
import polyak.Levels.Geometry.LevelZeroExclusive
import polyak.ModeLocking.Analysis.Perturbation

/-! At an arbitrary tongue tip the lag-one symbol has precisely the two
nondegenerate zeros required by the three-lag perturbation argument. -/
noncomputable section
namespace polyak.GapEdges
open General Levels ModeLocking Set Filter
open scoped Topology

structure Tip (q : Tuning) (k : ℕ) : Prop where
  period_ge : 3 ≤ k
  frontier : q ∈ frontier {p : Tuning | Regions.OmegaOne p}
  phase : q.angle (2 * Real.pi / k) = Real.pi / k

namespace Tip
variable {q : Tuning} {k : ℕ} (T : Tip q k)
include T

def frequency : Frequency := FareyPlateau.Edge.atom 1 k
  (by have := T.period_ge; omega) (by have := T.period_ge; omega)

theorem frequency_coe : (T.frequency : ℝ) = 2 * Real.pi / k := by
  change 2 * Real.pi * (1 : ℕ) / k = _
  norm_num

theorem frequency_mem : (T.frequency : ℝ) ∈ Ioo (0 : ℝ) Real.pi := by
  exact ⟨FareyPlateau.Edge.atom_pos (by norm_num) (by have := T.period_ge; omega) _,
    FareyPlateau.Edge.atom_lt_pi (by have := T.period_ge; omega) (by have := T.period_ge; omega)⟩

theorem weak (ω : Frequency) : (ω : ℝ) / 2 ≤ Geometry.shiftedCurve q 0 ω := by
  by_cases hz : (ω : ℝ) = 0
  · simp only [hz, Geometry.shiftedCurve_apply, Geometry.shiftedAngle_zero]
    simpa only [zero_div] using Real.pi_pos.le
  · rw [Geometry.shiftedCurve_zero, tuningCurve_apply]
    exact Regions.weak_omegaOne_angle_ge q
      (Regions.closure_omegaOne_subset_weak (frontier_subset_closure T.frontier))
      ⟨lt_of_le_of_ne ω.property.1 (Ne.symm hz), ω.property.2⟩

theorem shifted_phase : Geometry.shiftedCurve q 0 T.frequency = Real.pi / k := by
  rw [Geometry.shiftedCurve_zero, tuningCurve_apply, T.frequency_coe]
  exact T.phase

theorem closedDip_singleton : Geometry.closedDip (Geometry.shiftedCurve q 0) = {T.frequency} := by
  have he : Geometry.dip (Geometry.shiftedCurve q 0) = ∅ := by
    ext ω
    simp only [Geometry.dip, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (T.weak ω)
  have hm : T.frequency ∈ Geometry.closedDip (Geometry.shiftedCurve q 0) := by
    change Geometry.shiftedCurve q 0 T.frequency ≤ (T.frequency : ℝ) / 2
    rw [T.shifted_phase, T.frequency_coe]
    exact le_of_eq (by ring)
  obtain ⟨ω, hω⟩ := Geometry.closedDip_singleton_of_dip_empty q 0 ⟨_, hm⟩ he
  have hωeq : ω = T.frequency := by
    rw [hω, mem_singleton_iff] at hm
    exact hm.symm
  rwa [hωeq] at hω

theorem phase_actual : TwoLag.phase q 0 (T.frequency : ℝ) = Real.pi / k := by
  rw [TwoLag.phase, Geometry.jointAngle_actual q 0 T.frequency.property]
  exact T.shifted_phase

theorem phase_local : TwoLag.phase q 0 =ᶠ[𝓝 (T.frequency : ℝ)] Geometry.shiftedAngle q 0 := by
  filter_upwards [Ioo_mem_nhds T.frequency_mem.1 T.frequency_mem.2] with x hx
  exact Geometry.jointAngle_actual q 0 ⟨hx.1.le, hx.2.le⟩

theorem phase_deriv : deriv (TwoLag.phase q 0) T.frequency = 1 / 2 := by
  have hmin : IsLocalMin (fun x : ℝ => TwoLag.phase q 0 x - x / 2) (T.frequency : ℝ) := by
    filter_upwards [Ioo_mem_nhds T.frequency_mem.1 T.frequency_mem.2] with x hx
    have hw := T.weak ⟨x, hx.1.le, hx.2.le⟩
    rw [T.phase_actual, T.frequency_coe]
    have hp : TwoLag.phase q 0 x = Geometry.shiftedCurve q 0 ⟨x, hx.1.le, hx.2.le⟩ :=
      Geometry.jointAngle_actual q 0 ⟨hx.1.le, hx.2.le⟩
    rw [hp]
    change x / 2 ≤ Geometry.shiftedCurve q 0 ⟨x, hx.1.le, hx.2.le⟩ at hw
    have he : Real.pi / (k : ℝ) - 2 * Real.pi / k / 2 = 0 := by ring
    rw [he]
    exact sub_nonneg.mpr hw
  have hd := hmin.hasDerivAt_eq_zero
    ((TwoLag.analyticAt_phase q 0 T.frequency.property).differentiableAt.hasDerivAt.sub
      ((hasDerivAt_id (T.frequency : ℝ)).div_const 2))
  linarith

theorem phase_curvature : 0 < deriv^[2] (TwoLag.phase q 0) T.frequency := by
  have he := T.phase_local.iteratedDeriv_eq 2
  simp only [iteratedDeriv_eq_iterate] at he
  rw [he]
  apply Geometry.shiftedAngle_second_pos q 0 T.frequency_mem
  have hp : Geometry.shiftedAngle q 0 (T.frequency : ℝ) = Real.pi / k := T.shifted_phase
  rw [hp]
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by have := T.period_ge; omega)
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hk

theorem lag_trig {n : ℤ} (hn : n % (k : ℤ) = 1) :
    Real.sin ((n : ℝ) * (T.frequency : ℝ) - TwoLag.phase q 0 T.frequency) =
        Real.sin (Real.pi / k) ∧
      Real.cos ((n : ℝ) * (T.frequency : ℝ) - TwoLag.phase q 0 T.frequency) =
        Real.cos (Real.pi / k) := by
  have hh := FareyPlateau.Edge.lag_trig_reduce (j := 1) (k := k)
    (by have := T.period_ge; omega) (by have := T.period_ge; omega) n
    (TwoLag.phase q 0 T.frequency)
  change _ ∧ _ at hh
  simp only [Nat.cast_one, mul_one, hn, Int.cast_one, T.phase_actual] at hh
  have he : 2 * Real.pi / (k : ℝ) - Real.pi / k = Real.pi / k := by ring
  rw [he] at hh
  rw [T.phase_actual]
  exact ⟨hh.2, hh.1⟩

theorem lag_first {n : ℤ} (hn : n % (k : ℤ) = 1) :
    deriv (lagExtension q 0 n) T.frequency = Real.sin (Real.pi / k) * ((n : ℝ) - 1) := by
  change deriv (Geometry.extendedLag (TwoLag.phase q 0) n) T.frequency = _
  rw [FareyPlateau.Edge.lag_first_position_one
    (TwoLag.analyticAt_phase q 0 T.frequency.property) T.phase_actual n (T.lag_trig hn).1,
    T.phase_deriv]
  ring

theorem lag_second {n : ℤ} (hn : n % (k : ℤ) = 1) :
    deriv^[2] (lagExtension q 0 n) T.frequency =
      Real.cos (Real.pi / k) * (n : ℝ) * ((n : ℝ) - 1) -
        2 * Real.sin (Real.pi / k) * deriv^[2] (TwoLag.phase q 0) T.frequency := by
  change deriv^[2] (Geometry.extendedLag (TwoLag.phase q 0) n) T.frequency = _
  rw [FareyPlateau.Edge.lag_second_position_one
    (TwoLag.analyticAt_phase q 0 T.frequency.property) T.phase_actual n
    (T.lag_trig hn).1 (T.lag_trig hn).2, T.phase_deriv]
  ring

theorem lag_zero {n : ℤ} (hn : n % (k : ℤ) = 1) : lagExtension q 0 n T.frequency = 0 := by
  change Real.cos (TwoLag.phase q 0 T.frequency) -
    Real.cos ((n : ℝ) * (T.frequency : ℝ) - TwoLag.phase q 0 T.frequency) = 0
  rw [(T.lag_trig hn).2, T.phase_actual, sub_self]

theorem lag_one_strict {x : ℝ} (hx : 0 < x) (hxπ : x ≤ Real.pi)
    (hne : x ≠ (T.frequency : ℝ)) : lagExtension q 0 1 x < 0 := by
  let ω : Frequency := ⟨x, hx.le, hxπ⟩
  change lagExtension q 0 1 ω < 0
  rw [lagExtension_actual]
  apply Geometry.lag_one_neg_outside (Geometry.shiftedCurve q 0)
  · rw [T.closedDip_singleton, mem_singleton_iff]
    exact fun he => hne (congrArg Subtype.val he)
  · exact fun he => hx.ne' (congrArg Subtype.val he)

theorem lag_one_curvature : deriv^[2] (lagExtension q 0 1) T.frequency < 0 := by
  rw [T.lag_second (Int.emod_eq_of_lt (by norm_num) (by have := T.period_ge; omega))]
  norm_num only [Int.cast_one, sub_self, mul_zero, zero_sub]
  apply neg_neg_of_pos
  exact mul_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by exact_mod_cast (show 0 < k by have := T.period_ge; omega)))
    (div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < k by have := T.period_ge; omega)))))
    T.phase_curvature

end Tip
end polyak.GapEdges
