import jacobi.Analysis.UniformMeshIntegral

/-!
Article: jacobi, Proposition C.3.
Source: Lebesgue dominated convergence and chebyshev1's exact step integral.
Use: the original Cholesky GL residual and target eigenvector row transform pass their genuine growing finite sums to physical integrals.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory chebyshev1.Analysis
open scoped Topology

/-- Bounded actual mesh arrays converge to the integral of their
almost-everywhere moving-mesh limit, along any cofinal mesh sizes.
Use: the original Cholesky GL residual and target eigenvector row
transform pass their genuine growing finite sums to physical integrals.
Article: jacobi, Proposition C.3.
Proof: represent the actual finite sum by its exact original floor-step
integral. The countable floor mesh is measurable, the given uniform
bound is integrable on the true unit interval, and dominated convergence
applies to its genuine almost-everywhere pointwise limit. -/
theorem bounded_mesh_limit {ι:Type*} {l:Filter ι} [l.IsCountablyGenerated]
    (n:ι→ℕ) (a:ι→ℕ→ℝ) (f:ℝ→ℝ) (hn:Tendsto n l atTop)
    {B:ℝ} (hb:∀ᶠ i in l, ∀ j, |a i j|≤B)
    (hp:∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun i => a i (Nat.floor ((n i:ℝ)*t))) l (𝓝 (f t))) :
    Tendsto (fun i => (∑ j∈Finset.range (n i), a i j)/(n i:ℝ)) l
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  -- All moving arrays are integrated on the same fixed Lebesgue unit interval.
  let μ := volume.restrict (Ioo (0:ℝ) 1)
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ:=μ)
    (bound:=fun _ => B) (F:=fun i t => uniformStep (n i) (a i) t) (f:=f)
    (Eventually.of_forall (fun i =>
      ((measurable_of_countable (a i)).comp
        (Nat.measurable_floor.comp (by fun_prop))).aestronglyMeasurable))
    (hb.mono (fun i hi => Eventually.of_forall (fun t => by
      simpa only [uniformStep,Real.norm_eq_abs] using hi (Nat.floor ((n i:ℝ)*t)))))
    (integrable_const _) hp
  have hs := hlim.congr' (by
    filter_upwards [hn.eventually_gt_atTop 0] with i hi
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      ← restrict_Ioo_eq_restrict_Ioc,μ] using uniformStep_integral (n i) (a i) hi)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← restrict_Ioo_eq_restrict_Ioc,μ] using hs

end
end jacobi.Analysis
