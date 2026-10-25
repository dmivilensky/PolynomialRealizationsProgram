import polyak.FareyPlateau.FanAnalysis.JetCalculus

/-! A robust two-atom separating dual. The origin constraints pin the limiting
mass ratio; adding a positive multiple of one of them to the adjacent dual
makes both atom coefficients strictly negative. No bound on normalized mass
corrections is assumed. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

theorem negative_weighted_sum {a b wa wc : ℝ} (ha : a < 0) (hb : b < 0)
    (hwa : 0 ≤ wa) (hwc : 0 ≤ wc) (hn : 0 < wa + wc) : wa*a+wc*b < 0 := by
  by_cases haw : 0 < wa
  · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg haw ha) (mul_nonpos_of_nonneg_of_nonpos hwc hb.le)
  · have hcz : 0 < wc := by linarith
    exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hwa ha.le) (mul_neg_of_pos_of_neg hcz hb)

theorem eventual_two_atom_separation {D₁ D₂ P₁ P₂ M₁ M₂ : ℝ → ℝ} {a b m t : ℝ}
    (hm : 0 < m) (ht : 0 < t) (hne : m*a+b < 0)
    (hD₁ : Tendsto (fun δ => D₁ δ/δ^2) (𝓝[≠] 0) (𝓝 a))
    (hD₂ : Tendsto (fun δ => D₂ δ/δ^2) (𝓝[≠] 0) (𝓝 b))
    (hP₁ : Tendsto (fun δ => P₁ δ/δ) (𝓝[≠] 0) (𝓝 (-t)))
    (hP₂ : Tendsto (fun δ => P₂ δ/δ) (𝓝[≠] 0) (𝓝 (m*t)))
    (hM₁ : Tendsto (fun δ => M₁ δ/δ) (𝓝[≠] 0) (𝓝 t))
    (hM₂ : Tendsto (fun δ => M₂ δ/δ) (𝓝[≠] 0) (𝓝 (-m*t))) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀ wa wc : ℝ, 0 ≤ wa → 0 ≤ wc → 0 < wa+wc →
      ¬ (0 ≤ wa*D₁ δ+wc*D₂ δ ∧ 0 ≤ wa*P₁ δ+wc*P₂ δ ∧ 0 ≤ wa*M₁ δ+wc*M₂ δ) := by
  let x := (a-b)/(t*(m+1))
  have hden : t*(m+1) ≠ 0 := by positivity
  have hc : (m*a+b)/(m+1) < 0 := by exact div_neg_of_neg_of_pos hne (by linarith)
  have he₁ : a+x*(-t) = (m*a+b)/(m+1) := by dsimp [x]; field_simp; ring
  have he₂ : b+x*(m*t) = (m*a+b)/(m+1) := by dsimp [x]; field_simp; ring
  have he₃ : a-x*t = (m*a+b)/(m+1) := by linarith
  have he₄ : b-x*(-m*t) = (m*a+b)/(m+1) := by linarith
  have hp₁ := hD₁.add (hP₁.const_mul x)
  have hp₂ := hD₂.add (hP₂.const_mul x)
  have hm₁ := hD₁.sub (hM₁.const_mul x)
  have hm₂ := hD₂.sub (hM₂.const_mul x)
  rw [he₁] at hp₁
  rw [he₂] at hp₂
  rw [he₃] at hm₁
  rw [he₄] at hm₂
  filter_upwards [hp₁.eventually (eventually_lt_nhds hc), hp₂.eventually (eventually_lt_nhds hc),
    hm₁.eventually (eventually_lt_nhds hc), hm₂.eventually (eventually_lt_nhds hc), self_mem_nhdsWithin]
    with δ hp₁ hp₂ hm₁ hm₂ hδ wa wc hwa hwc hwn hfeas
  have hz : δ ≠ 0 := hδ
  have hsq : 0 < δ^2 := sq_pos_of_ne_zero hz
  have hpa : D₁ δ+x*δ*P₁ δ < 0 := by
    have hh : D₁ δ/δ^2+x*(P₁ δ/δ) = (D₁ δ+x*δ*P₁ δ)/δ^2 := by field_simp
    rw [hh] at hp₁
    simpa only [zero_mul] using (div_lt_iff₀ hsq).mp hp₁
  have hpc : D₂ δ+x*δ*P₂ δ < 0 := by
    have hh : D₂ δ/δ^2+x*(P₂ δ/δ) = (D₂ δ+x*δ*P₂ δ)/δ^2 := by field_simp
    rw [hh] at hp₂
    simpa only [zero_mul] using (div_lt_iff₀ hsq).mp hp₂
  have hma : D₁ δ-x*δ*M₁ δ < 0 := by
    have hh : D₁ δ/δ^2-x*(M₁ δ/δ) = (D₁ δ-x*δ*M₁ δ)/δ^2 := by field_simp
    rw [hh] at hm₁
    simpa only [zero_mul] using (div_lt_iff₀ hsq).mp hm₁
  have hmc : D₂ δ-x*δ*M₂ δ < 0 := by
    have hh : D₂ δ/δ^2-x*(M₂ δ/δ) = (D₂ δ-x*δ*M₂ δ)/δ^2 := by field_simp
    rw [hh] at hm₂
    simpa only [zero_mul] using (div_lt_iff₀ hsq).mp hm₂
  by_cases hx : 0 ≤ x*δ
  · have hh := negative_weighted_sum hpa hpc hwa hwc hwn
    have hpos := mul_nonneg hx hfeas.2.1
    nlinarith [hfeas.1]
  · have hh := negative_weighted_sum hma hmc hwa hwc hwn
    have hpos := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hx)) hfeas.2.2
    nlinarith [hfeas.1]

end polyak.FareyPlateau.FanAnalysis
