import polyak.FareyPlateau.FanAnalysis.FiniteTests
import polyak.FareyPlateau.FanAnalysis.Away
import polyak.FareyPlateau.FanAnalysis.SignedLattice

/-! Complete all-grid sufficiency for the actual fan constraint.
Convexity controls every local lattice point, including indices of order 1/delta. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking Set Filter
open scoped Topology
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem phi_zero (e δ : ℝ) : phi A e δ 0 = 0 := by
  simp only [phi, constraint, zero_sub, Real.cos_neg, sub_self, mul_zero, zero_add, mul_zero]

theorem baseline_second (e θ : ℝ) :
    constraintSecond ((k : ℝ) - 1) (correction A) (nearAngle A e) (farAngle A e) 0 θ =
      deriv^[2] (Fan.polynomial k) θ := by
  rw [Fan.polynomial_second]
  unfold constraintSecond
  rw [near_value A e, far_value A e]
  simp only [mul_zero, add_zero]

theorem eventually_linear_inside (τ B r : ℝ) (hr : 0 < r) :
    ∀ᶠ δ : ℝ in 𝓝 0, τ + B * δ ∈ Icc (τ - r) (τ + r) := by
  have hc : ContinuousAt (fun δ : ℝ => τ + B * δ) 0 := by fun_prop
  have hn : Ioo (τ - r) (τ + r) ∈ 𝓝 (τ + B * 0) := by
    simpa only [mul_zero, add_zero] using Ioo_mem_nhds (show τ - r < τ by linarith) (show τ < τ + r by linarith)
  filter_upwards [hc.eventually hn] with δ hδ
  exact ⟨hδ.1.le, hδ.2.le⟩

theorem all_grid_nonnegative {e : ℝ} (he : e < critical A) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀ θ ∈ Icc (-Real.pi) Real.pi,
      (∃ n : ℤ, θ = (n : ℝ) * k * δ) →
      (∃ n : ℤ, θ = 2 * Real.pi / k + ((A.lower : ℝ) + (n : ℝ) * k) * δ) →
      0 ≤ phi A e δ θ := by
  have ha := (near_analytic A e).continuousAt
  have hc := (far_analytic A e).continuousAt
  have hp := Fan.polynomial_second_roots_pos A.period_ge
  have hp0 : 0 < constraintSecond ((k : ℝ) - 1) (correction A) (nearAngle A e) (farAngle A e) 0 0 := by
    rw [baseline_second]
    exact hp.1
  have hp1 : 0 < constraintSecond ((k : ℝ) - 1) (correction A) (nearAngle A e) (farAngle A e) 0 (2 * Real.pi / k) := by
    rw [baseline_second]
    exact hp.2
  obtain ⟨r₀, hr₀, hconv₀⟩ := local_convex ha hc hp0
  obtain ⟨r₁, hr₁, hconv₁⟩ := local_convex ha hc hp1
  let r := min r₀ r₁ / 2
  have hr : 0 < r := div_pos (lt_min hr₀ hr₁) (by norm_num)
  have hrr0 : r ≤ r₀ := by dsimp [r]; nlinarith [min_le_left r₀ r₁]
  have hrr1 : r ≤ r₁ := by dsimp [r]; nlinarith [min_le_right r₀ r₁]
  have hAbs : ContinuousAt (fun δ : ℝ => |δ|) 0 := continuous_abs.continuousAt
  have hd0 : ∀ᶠ δ : ℝ in 𝓝 0, |δ| < r₀ :=
    hAbs.eventually (eventually_lt_nhds (show |(0 : ℝ)| < r₀ by simpa only [abs_zero] using hr₀))
  have hd1 : ∀ᶠ δ : ℝ in 𝓝 0, |δ| < r₁ :=
    hAbs.eventually (eventually_lt_nhds (show |(0 : ℝ)| < r₁ by simpa only [abs_zero] using hr₁))
  have haway := eventually_positive_away A.period_ge hr ha hc (near_value A e) (far_value A e)
    (z := correction A)
  have hm1 := eventually_linear_inside (2 * Real.pi / k) ((A.lower : ℝ) - k) r₁ hr₁
  have h2 := eventually_linear_inside (2 * Real.pi / k) ((A.lower : ℝ) + 2 * k) r₁ hr₁
  have hzleft := eventually_linear_inside 0 (-(k : ℝ)) r₀ hr₀
  have hzright := eventually_linear_inside 0 (k : ℝ) r₀ hr₀
  filter_upwards [hd0.filter_mono nhdsWithin_le_nhds, hd1.filter_mono nhdsWithin_le_nhds,
    haway.filter_mono nhdsWithin_le_nhds, hm1.filter_mono nhdsWithin_le_nhds,
    h2.filter_mono nhdsWithin_le_nhds, hzleft.filter_mono nhdsWithin_le_nhds,
    hzright.filter_mono nhdsWithin_le_nhds, core_tests A he, outer_tests A e, zero_neighbors A e]
    with δ hδ0 hδ1 hawayδ hm1δ h2δ hzl hzr hcore houter hzero θ hθ hgrid0 hgrid1
  have hfc0 : ConvexOn ℝ (Icc (0 - r₀) (0 + r₀)) (phi A e δ) := (hconv₀ δ hδ0).convexOn
  have hfc1 : ConvexOn ℝ (Icc (2 * Real.pi / k - r₁) (2 * Real.pi / k + r₁)) (phi A e δ) :=
    (hconv₁ δ hδ1).convexOn
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := A.period_ge; omega)
  by_cases hnear0 : |θ| < r
  · obtain ⟨n, hn⟩ := hgrid0
    by_cases hn0 : n = 0
    · simp only [hn0, Int.cast_zero, zero_mul] at hn
      rw [hn, phi_zero]
    · rw [hn]
      apply (signed_zero_lattice hfc0 hkR _ _ (phi_zero A e δ) hzero.2 hzero.1 n _ hn0).le
      · simpa only [zero_add, zero_sub, neg_mul] using hzl
      · simpa only [zero_add, zero_sub] using hzr
      · rw [← hn]
        exact ⟨by have := (abs_lt.mp hnear0).1; linarith, by have := (abs_lt.mp hnear0).2; linarith⟩
  by_cases hnear1 : |θ - 2 * Real.pi / k| < r
  · obtain ⟨n, hn⟩ := hgrid1
    rw [hn]
    apply (signed_edge_lattice hfc1 hkR hm1δ h2δ hcore.1 hcore.2 _ _ n _).le
    · simpa only [site, Int.cast_zero, zero_mul, add_zero, Int.cast_neg, Int.cast_one, neg_one_mul,
        sub_eq_add_neg] using houter.1
    · simpa only [site, Int.cast_one, Int.cast_ofNat, one_mul] using houter.2
    · rw [← hn]
      exact ⟨by have := (abs_lt.mp hnear1).1; linarith, by have := (abs_lt.mp hnear1).2; linarith⟩
  exact (hawayδ θ ⟨hθ, le_of_not_gt hnear0, le_of_not_gt hnear1⟩).le

end polyak.FareyPlateau.FanAnalysis.Actual
