import krylov.LotkaVolterra.CooperativeBarrier
import krylov.LotkaVolterra.RegionInvariance

/-!
Article: main_krylov, apC:prop:LV, the closed upper region.
Use: prove backward invariance including both edges and the saddle corner.
The coordinates x=s-sF and y=gamma*U-s+1 form a cooperative linear system
along each actual reversed orbit. Nonnegativity therefore follows from the
proved exponential barrier argument, without assuming a strictly interior start.
Source: the exact LV equations and closed-quadrant cooperative invariance.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set

private theorem upper_gap_reverse_algebra {γ : ℝ} (hγ : γ ≠ 1) (s U : ℝ) :
    sRate γ s U - γ * uRate s U =
      ((1 - γ) * U) * (s - saddleS γ) + (U - 2 * s) * (γ * U - s + 1) := by
  unfold sRate uRate saddleS
  field_simp
  ring

/-- The source's entire closed upper wedge is backward invariant along
genuine LV solutions, including boundary data and the equilibrium. -/
theorem upperRegion_backward_invariant {γ l r t₀ t : ℝ} {α : ℝ → ℝ × ℝ}
    (hγ : 0 < γ) (hγ₁ : γ < 1) (hα : IsSolutionOn γ α (Ioo l r))
    (ht₀ : t₀ ∈ Ioo l r) (hinit : α t₀ ∈ upperRegion γ)
    (ht : t ∈ Ioo l r) (htt : t ≤ t₀) : α t ∈ upperRegion γ := by
  have hpos := solution_positive_on_interval hα ht₀
    (upperRegion_subset_positiveQuadrant hγ hγ₁ hinit)
  let s : ℝ → ℝ := fun u ↦ (α (t₀ - u)).1
  let U : ℝ → ℝ := fun u ↦ (α (t₀ - u)).2
  have htime (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) : t₀ - u ∈ Ioo l r :=
    ⟨by linarith [ht.1, hu.2], by linarith [ht₀.2, hu.1]⟩
  have hs (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
      HasDerivAt s (-sRate γ (s u) (U u)) u := by
    have hh := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt _
      (hα _ (htime u hu))
    convert! hh.comp u ((hasDerivAt_id u).const_sub t₀) using 1
    simp [vectorField, s, U]
  have hU (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
      HasDerivAt U (-uRate (s u) (U u)) u := by
    have hh := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt _
      (hα _ (htime u hu))
    convert! hh.comp u ((hasDerivAt_id u).const_sub t₀) using 1
    simp [vectorField, s, U]
  have hcS := HasDerivAt.continuousOn hs
  have hcU := HasDerivAt.continuousOn hU
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image
    ((hcS.const_mul 2).sup (((hcU.const_mul (1 - γ)).add hcU).sub (hcS.const_mul 2)))
  have hds (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
      HasDerivAt (fun u ↦ s u - saddleS γ)
        ((0 : ℝ) * (s u - saddleS γ) + (2 * s u) * (γ * U u - s u + 1)) u := by
    convert! (hs u hu).sub_const (saddleS γ) using 1
    dsimp [sRate]
    ring
  have hdg (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
      HasDerivAt (fun u ↦ γ * U u - s u + 1)
        (((1 - γ) * U u) * (s u - saddleS γ) +
          (U u - 2 * s u) * (γ * U u - s u + 1)) u := by
    convert! (((hU u hu).const_mul γ).sub (hs u hu)).add_const 1 using 1
    have hh := upper_gap_reverse_algebra (ne_of_lt hγ₁) (s u) (U u)
    linarith
  have hsum (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
      0 + 2 * s u ≤ K ∧ (1 - γ) * U u + (U u - 2 * s u) ≤ K := by
    have hh := hK ⟨u, hu, rfl⟩
    constructor
    · simpa only [zero_add] using (le_max_left (2 * s u)
        ((1 - γ) * U u + U u - 2 * s u)).trans hh
    · have hb := (le_max_right (2 * s u) ((1 - γ) * U u + U u - 2 * s u)).trans hh
      linarith
  have hb := pair_nonnegative_cooperative (show (0 : ℝ) ≤ t₀ - t by linarith) hds hdg
    (fun u hu ↦ mul_nonneg (by norm_num) (hpos _ (htime u hu)).1.le)
    (fun u hu ↦ mul_nonneg (by linarith : 0 ≤ 1 - γ) (hpos _ (htime u hu)).2.le)
    hsum (show 0 ≤ s 0 - saddleS γ by simpa [s] using sub_nonneg.mpr hinit.1)
    (show 0 ≤ γ * U 0 - s 0 + 1 by
      have hh := (div_le_iff₀ hγ).mp hinit.2
      dsimp [s, U]
      simp only [sub_zero]
      nlinarith)
  change 0 ≤ (α (t₀ - (t₀ - t))).1 - saddleS γ ∧
    0 ≤ γ * (α (t₀ - (t₀ - t))).2 - (α (t₀ - (t₀ - t))).1 + 1 at hb
  have htimeeq : t₀ - (t₀ - t) = t := by ring
  rw [htimeeq] at hb
  refine ⟨by linarith [hb.1], (div_le_iff₀ hγ).mpr ?_⟩
  linarith [hb.2]

end
end krylov.LotkaVolterra
