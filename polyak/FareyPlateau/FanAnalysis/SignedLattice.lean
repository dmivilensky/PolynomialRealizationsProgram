import polyak.FareyPlateau.FanAnalysis.ConvexLattice

/-! Affine pullback handles both fan signs in one complete-lattice argument. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Set

theorem signed_edge_lattice {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {τ n₁ k δ : ℝ} (hk : 0 < k)
    (hm1 : τ + (n₁ - k) * δ ∈ s) (h2 : τ + (n₁ + 2 * k) * δ ∈ s)
    (h0 : 0 < f (τ + n₁ * δ)) (h1 : 0 < f (τ + (n₁ + k) * δ))
    (hleft : f (τ + n₁ * δ) ≤ f (τ + (n₁ - k) * δ))
    (hright : f (τ + (n₁ + k) * δ) ≤ f (τ + (n₁ + 2 * k) * δ))
    (n : ℤ) (hn : τ + (n₁ + (n : ℝ) * k) * δ ∈ s) :
    0 < f (τ + (n₁ + (n : ℝ) * k) * δ) := by
  let g : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap (τ + n₁ * δ) (τ + n₁ * δ + δ)
  have hg (x : ℝ) : g x = τ + (n₁ + x) * δ := by
    simp only [g, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  have hconv := hf.comp_affineMap g
  have hm1' : (0 : ℝ) - k ∈ g ⁻¹' s := by
    change g (0 - k) ∈ s
    rw [hg]
    simpa only [zero_sub, sub_eq_add_neg, zero_add] using hm1
  have h2' : (0 : ℝ) + 2 * k ∈ g ⁻¹' s := by
    change g (0 + 2 * k) ∈ s
    rw [hg]
    simpa only [zero_add] using h2
  have h0' : 0 < (f ∘ g) 0 := by simpa only [Function.comp_def, hg, add_zero] using h0
  have h1' : 0 < (f ∘ g) (0 + k) := by simpa only [Function.comp_def, hg, zero_add] using h1
  have hl' : (f ∘ g) 0 ≤ (f ∘ g) (0 - k) := by
    simpa only [Function.comp_def, hg, add_zero, zero_sub, sub_eq_add_neg, zero_add] using hleft
  have hr' : (f ∘ g) (0 + k) ≤ (f ∘ g) (0 + 2 * k) := by
    simpa only [Function.comp_def, hg, zero_add] using hright
  have hn' : (0 : ℝ) + (n : ℝ) * k ∈ g ⁻¹' s := by
    change g (0 + (n : ℝ) * k) ∈ s
    rw [hg]
    simpa only [zero_add] using hn
  simpa only [Function.comp_def, hg, zero_add] using
    convex_lattice_from_four hconv hk hm1' h2' h0' h1' hl' hr' n hn'

theorem signed_zero_lattice {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {k δ : ℝ} (hk : 0 < k)
    (hm1 : -(k * δ) ∈ s) (h1 : k * δ ∈ s) (hzero : f 0 = 0)
    (hleft : 0 < f (-(k * δ))) (hright : 0 < f (k * δ))
    (n : ℤ) (hn : (n : ℝ) * k * δ ∈ s) (hn0 : n ≠ 0) :
    0 < f ((n : ℝ) * k * δ) := by
  let g := (δ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  have hg (x : ℝ) : g x = x * δ := by simp only [g, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul]; ring
  have hconv := hf.comp_linearMap g
  have hm1' : -k ∈ g ⁻¹' s := by change g (-k) ∈ s; rw [hg, neg_mul]; exact hm1
  have h1' : k ∈ g ⁻¹' s := by change g k ∈ s; rw [hg]; exact h1
  have hz : (f ∘ g) 0 = 0 := by simpa only [Function.comp_def, hg, zero_mul] using hzero
  have hl : 0 < (f ∘ g) (-k) := by simpa only [Function.comp_def, hg, neg_mul] using hleft
  have hr : 0 < (f ∘ g) k := by simpa only [Function.comp_def, hg] using hright
  have hn' : (n : ℝ) * k ∈ g ⁻¹' s := by change g ((n : ℝ) * k) ∈ s; rw [hg]; exact hn
  simpa only [Function.comp_def, hg] using convex_lattice_from_neighbors hconv hk hm1' h1' hz hl hr n hn' hn0

end polyak.FareyPlateau.FanAnalysis
