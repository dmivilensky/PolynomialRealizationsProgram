import polyak.FareyPlateau.FanAnalysis.CompactGeometry

/-! Uniform three-zone sufficiency for compact families of actual
tunings. The inputs are only six finite local lattice tests; the
conclusion controls every integer lag, including unbounded indices. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
open General Levels Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable {j k : ℕ} (B : CompactFamily.Data X j k)

omit [CompactSpace X] [Nonempty X] in
theorem phi_zero (ε δ : ℝ) (x : X) : B.phi ε x δ 0=0 := by
  simp only [phi,constraint,zero_sub,Real.cos_neg,sub_self,mul_zero,zero_add,mul_zero]

theorem uniform_all_grid_nonnegative (ε : ℝ)
    (hcore : ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀x : X,
      0<B.phi ε x δ (2*Real.pi/k+(B.lower:ℝ)*δ) ∧
      0<B.phi ε x δ (2*Real.pi/k+((B.lower:ℝ)+k)*δ))
    (houter : ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀x : X,
      B.phi ε x δ (2*Real.pi/k+(B.lower:ℝ)*δ)≤
        B.phi ε x δ (2*Real.pi/k+((B.lower:ℝ)-k)*δ) ∧
      B.phi ε x δ (2*Real.pi/k+((B.lower:ℝ)+k)*δ)≤
        B.phi ε x δ (2*Real.pi/k+((B.lower:ℝ)+2*k)*δ))
    (hzero : ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀x : X,
      0<B.phi ε x δ ((k:ℝ)*δ) ∧ 0<B.phi ε x δ (-((k:ℝ)*δ))) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀x : X,∀θ∈Icc (-Real.pi) Real.pi,
      (∃n : ℤ,θ=(n:ℝ)*k*δ) →
      (∃n : ℤ,θ=2*Real.pi/k+((B.lower:ℝ)+(n:ℝ)*k)*δ) →
      0≤B.phi ε x δ θ := by
  let A := B.adjacent (Classical.choice (inferInstance : Nonempty X))
  have hk : 3≤k := A.period_ge
  have hp := Fan.polynomial_second_roots_pos hk
  obtain ⟨r₀,hr₀,hconv₀⟩ := B.uniform_local_convex ε 0 hp.1
  obtain ⟨r₁,hr₁,hconv₁⟩ := B.uniform_local_convex ε (2*Real.pi/k) hp.2
  let r := min r₀ r₁/2
  have hr : 0<r := div_pos (lt_min hr₀ hr₁) (by norm_num)
  have hrr0 : r≤r₀ := by dsimp [r];nlinarith [min_le_left r₀ r₁]
  have hrr1 : r≤r₁ := by dsimp [r];nlinarith [min_le_right r₀ r₁]
  have hAbs : ContinuousAt (fun δ : ℝ=>|δ|) 0 := continuous_abs.continuousAt
  have hd0 : ∀ᶠ δ : ℝ in 𝓝 0,|δ|<r₀ :=
    hAbs.eventually (eventually_lt_nhds (show |(0:ℝ)|<r₀ by simpa only [abs_zero] using hr₀))
  have hd1 : ∀ᶠ δ : ℝ in 𝓝 0,|δ|<r₁ :=
    hAbs.eventually (eventually_lt_nhds (show |(0:ℝ)|<r₁ by simpa only [abs_zero] using hr₁))
  have haway := B.uniform_positive_away ε hr
  have hm1 := Actual.eventually_linear_inside (2*Real.pi/k) ((B.lower:ℝ)-k) r₁ hr₁
  have h2 := Actual.eventually_linear_inside (2*Real.pi/k) ((B.lower:ℝ)+2*k) r₁ hr₁
  have hzleft := Actual.eventually_linear_inside 0 (-(k:ℝ)) r₀ hr₀
  have hzright := Actual.eventually_linear_inside 0 (k:ℝ) r₀ hr₀
  filter_upwards [hd0.filter_mono nhdsWithin_le_nhds,hd1.filter_mono nhdsWithin_le_nhds,
    haway.filter_mono nhdsWithin_le_nhds,hm1.filter_mono nhdsWithin_le_nhds,
    h2.filter_mono nhdsWithin_le_nhds,hzleft.filter_mono nhdsWithin_le_nhds,
    hzright.filter_mono nhdsWithin_le_nhds,hcore,houter,hzero]
    with δ hδ0 hδ1 hawayδ hm1δ h2δ hzl hzr hcoreδ houterδ hzeroδ x θ hθ hgrid0 hgrid1
  have hfc0 : ConvexOn ℝ (Icc (0-r₀) (0+r₀)) (B.phi ε x δ) := (hconv₀ δ hδ0 x).convexOn
  have hfc1 : ConvexOn ℝ (Icc (2*Real.pi/k-r₁) (2*Real.pi/k+r₁)) (B.phi ε x δ) :=
    (hconv₁ δ hδ1 x).convexOn
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  by_cases hnear0 : |θ|<r
  · obtain ⟨n,hn⟩ := hgrid0
    by_cases hn0 : n=0
    · simp only [hn0,Int.cast_zero,zero_mul] at hn
      rw [hn,B.phi_zero]
    · rw [hn]
      apply (signed_zero_lattice hfc0 hkR _ _ (B.phi_zero ε δ x)
        (hzeroδ x).2 (hzeroδ x).1 n _ hn0).le
      · simpa only [zero_add,zero_sub,neg_mul] using hzl
      · simpa only [zero_add,zero_sub] using hzr
      · rw [←hn]
        exact ⟨by have := (abs_lt.mp hnear0).1;linarith,
          by have := (abs_lt.mp hnear0).2;linarith⟩
  by_cases hnear1 : |θ-2*Real.pi/k|<r
  · obtain ⟨n,hn⟩ := hgrid1
    rw [hn]
    apply (signed_edge_lattice hfc1 hkR hm1δ h2δ (hcoreδ x).1 (hcoreδ x).2
      (houterδ x).1 (houterδ x).2 n _).le
    rw [←hn]
    exact ⟨by have := (abs_lt.mp hnear1).1;linarith,
      by have := (abs_lt.mp hnear1).2;linarith⟩
  exact (hawayδ x θ ⟨hθ,le_of_not_gt hnear0,le_of_not_gt hnear1⟩).le

end polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
