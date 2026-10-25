import polyak.FareyPlateau.FanAnalysis.UniformConstraint
import polyak.FareyPlateau.Fan.Polynomial

/-! Uniform positivity away from both limiting fan zeros. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Set Filter
open scoped Topology

theorem representative_unique {θ a : ℝ} (hθ : θ ∈ Icc (-Real.pi) Real.pi)
    (ha0 : 0 ≤ a) (haπ : a < Real.pi) (l : ℤ) (he : θ = a + l * (2 * Real.pi)) : l = 0 := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hl | hl
  · have hlR : (l : ℝ) ≤ -1 := by exact_mod_cast (show l ≤ -1 by omega)
    have hh := mul_le_mul_of_nonneg_right hlR (by positivity : 0 ≤ 2 * Real.pi)
    linarith [hθ.1]
  · have hlR : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
    have hh := mul_le_mul_of_nonneg_right hlR (by positivity : 0 ≤ 2 * Real.pi)
    linarith [hθ.2, Real.pi_pos]

theorem baseline_polynomial {k : ℕ} (hk : 3 ≤ k) (θ : ℝ) :
    baseline ((k : ℝ) - 1) (Real.pi / k) θ = Fan.polynomial k θ := by
  have _ := hk
  unfold baseline cosineDefect Fan.polynomial
  rw [show -((k : ℝ) - 1) * θ - Real.pi / k = -(((k : ℝ) - 1) * θ + Real.pi / k) by ring,
    Real.cos_neg]
  ring

def awaySet (k : ℕ) (r : ℝ) : Set ℝ :=
  Icc (-Real.pi) Real.pi ∩ {θ | r ≤ |θ| ∧ r ≤ |θ - 2 * Real.pi / k|}

theorem away_compact (k : ℕ) (r : ℝ) : IsCompact (awaySet k r) := by
  apply isCompact_Icc.inter_right
  exact (isClosed_le continuous_const continuous_abs).inter
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)

theorem polynomial_positive_away {k : ℕ} (hk : 3 ≤ k) {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ awaySet k r) : 0 < Fan.polynomial k θ := by
  apply lt_of_le_of_ne (Fan.polynomial_nonneg hk θ)
  intro he
  obtain ⟨l, hl | hl⟩ := (Fan.polynomial_eq_zero_iff hk θ).mp he.symm
  · have hzero : l = 0 := representative_unique hθ.1 le_rfl Real.pi_pos l (by simpa only [zero_add] using hl)
    rw [hzero, Int.cast_zero, zero_mul] at hl
    have hh := hθ.2.1
    rw [hl, abs_zero] at hh
    linarith
  · have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hcpos : 0 ≤ 2 * Real.pi / k := by positivity
    have hcπ : 2 * Real.pi / k < Real.pi :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos])
    have hzero := representative_unique hθ.1 hcpos hcπ l hl
    rw [hzero, Int.cast_zero, zero_mul, add_zero] at hl
    have hh := hθ.2.2
    rw [hl, sub_self, abs_zero] at hh
    linarith

theorem away_margin {k : ℕ} (hk : 3 ≤ k) {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ awaySet k r, ε ≤ Fan.polynomial k θ := by
  by_cases hne : (awaySet k r).Nonempty
  · have hc : Continuous (Fan.polynomial k) := by unfold Fan.polynomial; fun_prop
    obtain ⟨θ, hθ, hmin⟩ := (away_compact k r).exists_isMinOn hne hc.continuousOn
    exact ⟨Fan.polynomial k θ, polynomial_positive_away hk hr hθ, hmin⟩
  · exact ⟨1, by norm_num, fun θ hθ => False.elim (hne ⟨θ, hθ⟩)⟩

theorem eventually_positive_away {k : ℕ} (hk : 3 ≤ k) {r z : ℝ} (hr : 0 < r)
    {a c : ℝ → ℝ} (ha : ContinuousAt a 0) (hc : ContinuousAt c 0)
    (ha0 : a 0 = Real.pi / k) (hc0 : c 0 = Real.pi / k) :
    ∀ᶠ δ in 𝓝 0, ∀ θ ∈ awaySet k r, 0 < constraint ((k : ℝ) - 1) z a c δ θ := by
  obtain ⟨ε, hε, hmargin⟩ := away_margin hk hr
  have hm : 0 ≤ (k : ℝ) - 1 := by
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have he := eventually_uniform_constraint_close (z := z) hm ha hc ha0 hc0 hε
  filter_upwards [he] with δ hδ θ hθ
  have hb := hmargin θ hθ
  have hnear := hδ θ
  rw [baseline_polynomial hk] at hnear
  have hh := (abs_lt.mp hnear).1
  linarith

end polyak.FareyPlateau.FanAnalysis
