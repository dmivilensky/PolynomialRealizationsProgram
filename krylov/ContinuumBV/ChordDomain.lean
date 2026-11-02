import krylov.ContinuumBV.StringPath
import krylov.ContinuumBV.UniformNeighborhood
import Mathlib.Analysis.Convex.Basic

/-!
Article: main_krylov, apC:lem:fund, localization of physical partition chords.
Use: a straight chord between admissible positive states may slightly leave
the nonlinear invariant K≤φp. Its distance from the true compact invariant
domain is controlled by the product of the two coordinate increments.
Source: the exact quadratic defect of a bilinear invariant on a chord.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set
open krylov.Strings
open scoped NNReal

/-- Every chord between two ordered admissible states stays close to the
admissible domain. Only the continuous φ increment must become small; the
other coordinates may have arbitrarily large fixed jumps. -/
theorem chord_near_compactStateDomain (M : Mass) (φ : ℝ → ℝ) (L : ℝ≥0)
    {u v w : PotentialState} (hu : u ∈ compactStateDomain M φ L)
    (hv : v ∈ compactStateDomain M φ L) (hφ : u.1 ≤ v.1) (hp : u.2.1 ≤ v.2.1)
    (hw : w ∈ segment ℝ u v) :
    ∃ q ∈ compactStateDomain M φ L, ‖w - q‖ ≤ (v.1 - u.1) * (v.2.1 - u.2.1) := by
  have hbconv : Convex ℝ (Icc 1 (φ L) ×ˢ
      (Icc 1 (integralSlope M.measure φ L) ×ˢ Icc 1 (integralEnergy M.measure φ L))) :=
    Convex.prod (convex_Icc 1 (φ L))
      (Convex.prod (convex_Icc 1 (integralSlope M.measure φ L))
        (convex_Icc 1 (integralEnergy M.measure φ L)))
  have hbox : w ∈ Icc 1 (φ L) ×ˢ
      (Icc 1 (integralSlope M.measure φ L) ×ˢ Icc 1 (integralEnergy M.measure φ L)) :=
    hbconv.segment_subset hu.1 hv.1 hw
  let q : PotentialState := (w.1, w.2.1, min w.2.2 (w.1 * w.2.1))
  have hprod : 1 ≤ w.1 * w.2.1 := by nlinarith [hbox.1.1, hbox.2.1.1]
  have hq : q ∈ compactStateDomain M φ L := by
    refine ⟨⟨hbox.1, hbox.2.1, le_min hbox.2.2.1 hprod,
      (min_le_left _ _).trans hbox.2.2.2⟩, ?_⟩
    exact min_le_right w.2.2 (w.1 * w.2.1)
  refine ⟨q, hq, ?_⟩
  have hD : 0 ≤ (v.1 - u.1) * (v.2.1 - u.2.1) := mul_nonneg (sub_nonneg.2 hφ) (sub_nonneg.2 hp)
  by_cases hkw : w.2.2 ≤ w.1 * w.2.1
  · have hqw : q = w := by simp only [q, min_eq_left hkw]
    rw [hqw, sub_self, norm_zero]
    exact hD
  · have hkw' : w.1 * w.2.1 ≤ w.2.2 := (lt_of_not_ge hkw).le
    have hn : ‖w - q‖ = w.2.2 - w.1 * w.2.1 := by
      simp only [q, min_eq_right hkw', Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
        sub_self, norm_zero, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hkw'),
        max_eq_right (sub_nonneg.2 hkw')]
    rw [hn]
    obtain ⟨θ, hθ, rfl⟩ := (segment_eq_image ℝ u v) ▸ hw
    change (1 - θ) * u.2.2 + θ * v.2.2 -
      ((1 - θ) * u.1 + θ * v.1) * ((1 - θ) * u.2.1 + θ * v.2.1) ≤ _
    have hlin : (1 - θ) * u.2.2 + θ * v.2.2 ≤
        (1 - θ) * (u.1 * u.2.1) + θ * (v.1 * v.2.1) :=
      add_le_add (mul_le_mul_of_nonneg_left hu.2 (sub_nonneg.2 hθ.2))
        (mul_le_mul_of_nonneg_left hv.2 hθ.1)
    have ht : θ * (1 - θ) ≤ 1 := by nlinarith [sq_nonneg θ]
    have hmul := mul_le_mul_of_nonneg_right ht hD
    nlinarith

/-- The invariant domain is convex on every fixed-φ slice. In particular,
the entire true atom chord remains in the original r≥1 graph domain. -/
theorem chord_mem_compactStateDomain_of_first_eq (M : Mass) (φ : ℝ → ℝ) (L : ℝ≥0)
    {u v w : PotentialState} (hu : u ∈ compactStateDomain M φ L)
    (hv : v ∈ compactStateDomain M φ L) (heq : u.1 = v.1)
    (hw : w ∈ segment ℝ u v) : w ∈ compactStateDomain M φ L := by
  have hnear : ∃ q ∈ compactStateDomain M φ L, ‖w - q‖ ≤ 0 := by
    by_cases hp : u.2.1 ≤ v.2.1
    · simpa only [heq, sub_self, zero_mul] using
        chord_near_compactStateDomain M φ L hu hv heq.le hp hw
    · simpa only [heq, sub_self, zero_mul] using
        chord_near_compactStateDomain M φ L hv hu heq.symm.le (le_of_not_ge hp)
          (segment_symm ℝ u v ▸ hw)
  obtain ⟨q, hq, hnorm⟩ := hnear
  have he : w = q := sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hnorm (norm_nonneg _)))
  exact he ▸ hq

end
end krylov.ContinuumBV
