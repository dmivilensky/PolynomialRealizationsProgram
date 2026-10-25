import polyak.General.Multipliers.Algebra

/-! A strictly negative continuous finite symbol has a uniform margin.
The balanced minimizer perturbation removes the multiplier's zero at 1. -/

namespace polyak.General.Multipliers
noncomputable section
open Set

theorem certificate_of_negative {m : C(Spectral.Frequency, ℂ)} {t : ℝ}
    (s : Finset ℕ) (alpha beta : ℕ → ℝ) (gp gm : ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n)
    (ha : ∀ n ∈ s, 0 ≤ alpha n) (hb : ∀ n ∈ s, 0 ≤ beta n)
    (hgp : 0 ≤ gp) (hgm : 0 ≤ gm)
    (hcancel : (∑ n ∈ s, (alpha n-beta n)*Real.sinh (n*t)) + gp-gm = 0)
    (hnegative : ∀ c, Duality.symbol m t s alpha beta gp gm c < 0) :
    Nonempty (Duality.StrictCertificate m t) := by
  let : Nonempty Spectral.Frequency := ⟨⟨0, by norm_num, by norm_num⟩⟩
  obtain ⟨c, _, hc⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    (Duality.continuous_symbol m t s alpha beta gp gm).continuousOn
  refine ⟨{
    lags := s
    positive_lag := hs
    α := alpha
    β := beta
    α_nonneg := ha
    β_nonneg := hb
    γplus := gp
    γminus := gm
    γplus_nonneg := hgp
    γminus_nonneg := hgm
    ε := -Duality.symbol m t s alpha beta gp gm c
    ε_pos := neg_pos.mpr (hnegative c)
    cancel := hcancel
    strict := ?_ }⟩
  intro w
  rw [neg_neg]
  exact hc (mem_univ w)

theorem balanced_perturbation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfn : ∀ x, f x ≤ 0) (hstrict : ∀ x, 0 ≤ g x → f x < 0) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ x, f x + 2*eta*g x < 0 := by
  classical
  let K : Set X := {x | 0 ≤ g x}
  have hK : IsCompact K := (isClosed_le continuous_const hg).isCompact
  obtain ⟨G, hG⟩ := isCompact_univ.bddAbove_image hg.continuousOn
  have hGb : ∀ x, g x ≤ max 1 G := fun x =>
    (hG ⟨x, mem_univ x, rfl⟩).trans (le_max_right _ _)
  have hGpos : 0 < max 1 G := zero_lt_one.trans_le (le_max_left _ _)
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hm⟩ := hK.exists_isMaxOn hne hf.continuousOn
    have hfx : f x < 0 := hstrict x hx
    have heta : 0 < -f x/(4*max 1 G) :=
      div_pos (neg_pos.mpr hfx) (mul_pos (by norm_num) hGpos)
    refine ⟨-f x/(4*max 1 G), heta, ?_⟩
    intro y
    by_cases hy : y ∈ K
    · have hm' : f y ≤ f x := hm hy
      have hmul : 2*(-f x/(4*max 1 G))*g y ≤ 2*(-f x/(4*max 1 G))*max 1 G :=
        mul_le_mul_of_nonneg_left (hGb y) (mul_nonneg (by norm_num) heta.le)
      have he : 2*(-f x/(4*max 1 G))*max 1 G = -f x/2 := by
        field_simp
        ring
      rw [he] at hmul
      linarith
    · have hgy : g y < 0 := lt_of_not_ge hy
      have hp : 0 < 2*(-f x/(4*max 1 G)) := mul_pos (by norm_num) heta
      exact add_neg_of_nonpos_of_neg (hfn y) (mul_neg_of_pos_of_neg hp hgy)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y
    have hy : g y < 0 := lt_of_not_ge (fun hy => hne ⟨y, hy⟩)
    nlinarith [hfn y]

end
end polyak.General.Multipliers
