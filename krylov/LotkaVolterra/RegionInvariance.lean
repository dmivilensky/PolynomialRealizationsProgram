import krylov.LotkaVolterra.Barrier
import krylov.LotkaVolterra.PositiveOrbits

/-!
Article: main_krylov, apC:prop:LV, actual backward region invariance.
Use: turn the computed outward boundary signs into statements about genuine
orbits. Local ODE uniqueness excludes finite contact with the saddle, so
the strict first-contact argument applies even at the common boundary corner.
Source: Picard uniqueness and the proved two-barrier first-contact theorem.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set

/-- A nonconstant actual orbit cannot reach an equilibrium in finite time. -/
theorem solution_ne_saddle_on_interval {γ l r t₀ : ℝ} {α : ℝ → ℝ × ℝ}
    (hγ : γ ≠ 1) (hα : IsSolutionOn γ α (Ioo l r)) (ht₀ : t₀ ∈ Ioo l r)
    (hinit : α t₀ ≠ saddlePoint γ) : ∀ t ∈ Ioo l r, α t ≠ saddlePoint γ := by
  intro t ht heq
  have heqflow := solution_unique_on_interval hα
    (show IsSolutionOn γ (fun _ ↦ saddlePoint γ) (Ioo l r) from fun u _ ↦ by
      rw [show vectorField γ (saddlePoint γ) = 0 from saddlePoint_isEquilibrium hγ]
      exact hasDerivAt_const u _) ht heq
  exact hinit (heqflow ht₀)

/-- The entire bounded lower region is backward invariant under the actual
LV flow, throughout every interval where that flow exists. -/
theorem lowerRegion_backward_invariant {γ l r t₀ t : ℝ} {α : ℝ → ℝ × ℝ}
    (hγ : 0 < γ) (hγ₁ : γ < 1) (hα : IsSolutionOn γ α (Ioo l r))
    (ht₀ : t₀ ∈ Ioo l r) (hinit : α t₀ ∈ lowerRegion γ)
    (ht : t ∈ Ioo l r) (htt : t ≤ t₀) : α t ∈ lowerRegion γ := by
  have hpos := solution_positive_on_interval hα ht₀
    (lowerRegion_subset_positiveQuadrant γ hinit)
  have hne := solution_ne_saddle_on_interval (ne_of_lt hγ₁) hα ht₀ (by
    intro heq
    have hs := hinit.2.1
    rw [heq] at hs
    exact lt_irrefl _ hs)
  have htime (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) : t₀ - u ∈ Ioo l r :=
    ⟨by linarith [ht.1, hu.2], by linarith [ht₀.2, hu.1]⟩
  have hs (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
      HasDerivAt (fun u ↦ (α (t₀ - u)).1)
        (-sRate γ (α (t₀ - u)).1 (α (t₀ - u)).2) u := by
    have hh := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt _
      (hα _ (htime u hu))
    convert! hh.comp u ((hasDerivAt_id u).const_sub t₀) using 1
    simp [vectorField]
  have hU (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
      HasDerivAt (fun u ↦ (α (t₀ - u)).2)
        (-uRate (α (t₀ - u)).1 (α (t₀ - u)).2) u := by
    have hh := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt _
      (hα _ (htime u hu))
    convert! hh.comp u ((hasDerivAt_id u).const_sub t₀) using 1
    simp [vectorField]
  have hb := pair_positive_invariant (show (0 : ℝ) ≤ t₀ - t by linarith)
    (fun u hu ↦ (hs u hu).const_sub (saddleS γ))
    (fun u hu ↦ ((hs u hu).add_const 1).sub (hU u hu))
    (show 0 < saddleS γ - (α (t₀ - 0)).1 by simpa using sub_pos.mpr hinit.2.1)
    (show 0 < (α (t₀ - 0)).1 + 1 - (α (t₀ - 0)).2 by
      simpa using sub_pos.mpr hinit.2.2.2)
    (fun u hu hf hg ↦ ?_) (fun u hu hg hf ↦ ?_)
  · change 0 < saddleS γ - (α (t₀ - (t₀ - t))).1 ∧
      0 < (α (t₀ - (t₀ - t))).1 + 1 - (α (t₀ - (t₀ - t))).2 at hb
    have hst : t₀ - (t₀ - t) = t := by ring
    rw [hst] at hb
    exact ⟨(hpos t ht).1, by linarith [hb.1], (hpos t ht).2, by linarith [hb.2]⟩
  · change 0 ≤ (α (t₀ - u)).1 + 1 - (α (t₀ - u)).2 at hg
    have hsA : (α (t₀ - u)).1 = saddleS γ := by linarith
    have hUB : (α (t₀ - u)).2 ≤ saddleU γ := by
      rw [saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)]
      linarith
    have hUne : (α (t₀ - u)).2 ≠ saddleU γ := by
      intro heq
      exact hne _ (htime u hu) (Prod.ext hsA heq)
    have hh := lower_vertical_outward hγ hγ₁ (lt_of_le_of_ne hUB hUne)
    simpa only [hsA, neg_neg] using hh
  · change (α (t₀ - u)).1 + 1 - (α (t₀ - u)).2 = 0 at hg
    have hdiag : (α (t₀ - u)).2 = (α (t₀ - u)).1 + 1 := by linarith
    have hh := lower_diagonal_outward hγ₁ (hpos _ (htime u hu)).1
      (show (α (t₀ - u)).1 < saddleS γ by linarith)
    rw [← hdiag] at hh
    convert hh using 1
    ring

end
end krylov.LotkaVolterra
