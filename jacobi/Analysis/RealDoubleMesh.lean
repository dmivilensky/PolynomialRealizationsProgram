import jacobi.Analysis.BoundedDoubleMesh

/-!
The real form of the existing bounded double-mesh integral limit.
Embedding real values into the complex theorem and taking real parts
reuses its complete dominated-convergence proof and moving cutoffs.
Use: the actual standard-flow initial energy derivative is a bounded
triangular double mesh of genuine Green entries.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
Article role: dominated convergence for the triangular real double mesh of Green entries.
Source: Lebesgue dominated convergence; the existing bounded complex double-mesh theorem.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual bounded real double mesh converges to its true nested
integral whenever the moving meshes converge almost everywhere.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
Source: Lebesgue dominated convergence; the existing bounded complex double-mesh theorem.
-/
theorem bounded_real_double_mesh_limit {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (n : ι → ℕ) (a : ι → ℕ → ℕ → ℝ) (K : ℝ → ℝ → ℝ) (hn : Tendsto n l atTop)
    {B : ℝ} (hb : ∀ᶠ i in l,∀ j k,|a i j k|≤B)
    (hp : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun i => a i (Nat.floor ((n i:ℝ)*r)) (Nat.floor ((n i:ℝ)*s))) l (𝓝 (K r s))) :
    Tendsto (fun i => (∑ j∈Finset.range (n i),∑ k∈Finset.range (n i),a i j k)/(n i:ℝ)^2)
      l (𝓝 (∫ r in (0:ℝ)..1,∫ s in (0:ℝ)..1,K r s)) := by
  have hb' : ∀ᶠ i in l,∀ j k,‖(a i j k:ℂ)‖≤B := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hb
  have hp' : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun i => (a i (Nat.floor ((n i:ℝ)*r)) (Nat.floor ((n i:ℝ)*s)):ℂ)) l (𝓝 (K r s:ℂ)) := by
    filter_upwards [hp] with r hr
    filter_upwards [hr] with s hs
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  have h := bounded_double_mesh_limit n (fun i j k => (a i j k:ℂ)) (fun r s => (K r s:ℂ)) hn hb' hp'
  have he (i : ι) : (∑ j∈Finset.range (n i),∑ k∈Finset.range (n i),(a i j k:ℂ))/(n i:ℂ)^2=
      (( (∑ j∈Finset.range (n i),∑ k∈Finset.range (n i),a i j k)/(n i:ℝ)^2:ℝ):ℂ) := by
    push_cast
    rfl
  simp only [he,intervalIntegral.integral_ofReal] at h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,Complex.ofReal_re] using hr

end
end jacobi.Analysis
