import polyak.ModeLocking.Localization.PotentialEnds
import Mathlib.Topology.Order.LeftRightNhds

/-! Compactness turns sharp local quadratic jets and divergent endpoint
potentials into a uniform sharp penalty for every competing finite grid. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Set Metric Filter
open scoped Topology

private theorem potential_away_margin {R : ℝ → ℝ} {a b : ℝ} {Z : Finset ℝ}
    (hR : ContinuousOn R (Ioo a b)) (hpos : ∀ x ∈ Ioo a b, x ∉ Z → 0 < R x)
    (hleft : Tendsto R (𝓝[>] a) atTop) (hright : Tendsto R (𝓝[<] b) atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ m > 0, ∀ x ∈ Ioo a b, δ ≤ infDist x (Z:Set ℝ) → m ≤ R x := by
  obtain ⟨u,hu,hRu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hleft.eventually_ge_atTop 1)
  obtain ⟨v,hv,hRv⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (hright.eventually_ge_atTop 1)
  let C : Set ℝ := Icc u v ∩ {x | δ ≤ infDist x (Z:Set ℝ)}
  have hC : IsCompact C := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_infDist_pt (Z:Set ℝ)))
  have hsub : C ⊆ Ioo a b := fun x hx => ⟨lt_of_lt_of_le hu hx.1.1, lt_of_le_of_lt hx.1.2 hv⟩
  by_cases hne : C.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hC.exists_isMinOn hne (hR.mono hsub)
    have hxnot : x ∉ Z := by
      intro hz
      have hd : infDist x (Z:Set ℝ) = 0 := infDist_zero_of_mem (show x ∈ (Z:Set ℝ) from hz)
      have hh : δ ≤ infDist x (Z:Set ℝ) := hx.2
      rw [hd] at hh
      linarith
    have hxpos := hpos x (hsub hx) hxnot
    refine ⟨min 1 (R x),lt_min (by norm_num) hxpos,?_⟩
    intro y hy hdist
    by_cases hlu : y < u
    · exact (min_le_left _ _).trans (hRu ⟨hy.1,hlu⟩)
    by_cases hrv : v < y
    · exact (min_le_left _ _).trans (hRv ⟨hrv,hy.2⟩)
    exact (min_le_right _ _).trans (hmin ⟨⟨le_of_not_gt hlu,le_of_not_gt hrv⟩,hdist⟩)
  · refine ⟨1,by norm_num,?_⟩
    intro y hy hdist
    by_cases hlu : y < u
    · exact hRu ⟨hy.1,hlu⟩
    by_cases hrv : v < y
    · exact hRv ⟨hrv,hy.2⟩
    exact False.elim (hne ⟨y,⟨le_of_not_gt hlu,le_of_not_gt hrv⟩,hdist⟩)

private theorem finite_local_radius (Z : Finset ℝ) (P : ℝ → ℝ → Prop)
    (hlocal : ∀ z ∈ Z, ∃ δ > 0, ∀ x, |x-z| < δ → P z x) :
    ∃ δ > 0, ∀ z ∈ Z, ∀ x, |x-z| < δ → P z x := by
  classical
  induction Z using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert z Z hz ih =>
    obtain ⟨r,hr,hbound⟩ := hlocal z (Finset.mem_insert_self _ _)
    obtain ⟨δ,hδ,hδbound⟩ := ih (fun y hy => hlocal y (Finset.mem_insert_of_mem hy))
    refine ⟨min r δ,lt_min hr hδ,?_⟩
    intro y hy x hx
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hbound x (hx.trans_le (min_le_left _ _))
    · exact hδbound y hy x (hx.trans_le (min_le_right _ _))

theorem quadratic_lower_of_limit {R : ℝ → ℝ} {z c C : ℝ}
    (hzero : R z=0) (hlim : Tendsto (fun x => R x/(x-z)^2) (𝓝[≠] z) (𝓝 C))
    (hc : c<C) : ∃ δ > 0, ∀ x, |x-z| < δ → c*(x-z)^2 ≤ R x := by
  have he : ∀ᶠ x in 𝓝[≠] z, c < R x/(x-z)^2 := hlim.eventually (eventually_gt_nhds hc)
  rw [eventually_nhdsWithin_iff] at he
  have hh : ∀ᶠ x in 𝓝 z, c*(x-z)^2 ≤ R x := by
    filter_upwards [he] with x hx
    by_cases hxz : x=z
    · subst x
      rw [sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,hzero]
    · exact ((lt_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hxz))).mp (hx hxz)).le
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hh
  exact ⟨δ,hδ,fun x hx => hball (by simpa only [Real.dist_eq] using hx)⟩

theorem sharp_potential_penalty {R : ℝ → ℝ} {a b c : ℝ} {Z : Finset ℝ}
    (hZ : Z.Nonempty) (hc : 0 < c)
    (hR : ContinuousOn R (Ioo a b)) (hpos : ∀ x ∈ Ioo a b, x ∉ Z → 0 < R x)
    (hleft : Tendsto R (𝓝[>] a) atTop) (hright : Tendsto R (𝓝[<] b) atTop)
    (hlocal : ∀ z ∈ Z, ∃ r > 0, ∀ x, |x-z| < r → c*(x-z)^2 ≤ R x) :
    ∃ δ > 0, ∀ d, 0 < d → d < δ → ∀ x ∈ Ioo a b,
      d ≤ infDist x (Z:Set ℝ) → c*d^2 ≤ R x := by
  obtain ⟨r,hr,hbound⟩ := finite_local_radius Z (fun z x => c*(x-z)^2 ≤ R x) hlocal
  obtain ⟨m,hm,haway⟩ := potential_away_margin hR hpos hleft hright hr
  let δ := min r (Real.sqrt (m/c))
  have hδ : 0 < δ := lt_min hr (Real.sqrt_pos.mpr (div_pos hm hc))
  refine ⟨δ,hδ,?_⟩
  intro d hd hdδ x hx hdist
  by_cases hnear : infDist x (Z:Set ℝ) < r
  · obtain ⟨z,hz,hzdist⟩ := Z.finite_toSet.isCompact.exists_infDist_eq_dist
      (by simpa only [Finset.coe_nonempty] using hZ) x
    have habs : |x-z| < r := by simpa only [hzdist,Real.dist_eq] using hnear
    have hsq : d^2 ≤ (x-z)^2 := by
      rw [hzdist,Real.dist_eq] at hdist
      nlinarith [sq_abs (x-z)]
    exact (mul_le_mul_of_nonneg_left hsq hc.le).trans (hbound z hz x habs)
  · have hdroot : d < Real.sqrt (m/c) := hdδ.trans_le (min_le_right _ _)
    have hdsq : d^2 < m/c := by
      have he := Real.sq_sqrt (div_pos hm hc).le
      nlinarith [Real.sqrt_nonneg (m/c)]
    have hcd : c*d^2 < m := by simpa only [mul_comm] using (lt_div_iff₀ hc).mp hdsq
    exact hcd.le.trans (haway x hx (le_of_not_gt hnear))

end polyak.ModeLocking.Localization
