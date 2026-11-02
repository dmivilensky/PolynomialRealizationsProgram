import jacobi.Analysis.ComplexMesh

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Bounded complex double mesh sums converge by two applications of
dominated convergence. The triangular cutoffs are included in the
finite data, so the fixed integration rectangle also covers the
moving endpoint and the ground-normalized singular corner.
Source: Lebesgue dominated convergence for bounded step functions.
Use: the finite normalized Volterra kernel is uniformly bounded before integration, and its moving-mesh limit is the actual ground-square ratio. This theorem passes the original nested finite sum to the original continuum nested operator.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- Uniformly bounded actual complex double meshes have the integral of their almost-everywhere pointwise limit.
Use: the finite normalized Volterra kernel is uniformly bounded before integration, and its moving-mesh limit is the actual ground-square ratio. This theorem passes the original nested finite sum to the original continuum nested operator.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: dominated convergence, applied to the two finite-measure unit intervals.
Proof: integrate each inner mesh by dominated convergence. Its integral has the same constant norm bound because the unit interval has length one. The outer functions remain measurable floor-mesh functions, so dominated convergence applies again. The exact complex double-mesh formula computes the original finite sums. -/
theorem bounded_double_mesh_limit {ι:Type*} {l:Filter ι} [l.IsCountablyGenerated]
    (n:ι→ℕ) (a:ι→ℕ→ℕ→ℂ) (K:ℝ→ℝ→ℂ) (hn:Tendsto n l atTop)
    {B:ℝ} (hb:∀ᶠi in l,∀j k,‖a i j k‖≤B)
    (hp:∀ᵐr ∂volume.restrict (Ioo (0:ℝ) 1),∀ᵐs ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun i => a i (Nat.floor ((n i:ℝ)*r)) (Nat.floor ((n i:ℝ)*s))) l (𝓝 (K r s))) :
    Tendsto (fun i => (∑j∈Finset.range (n i),∑k∈Finset.range (n i),a i j k)/(n i:ℂ)^2) l
      (𝓝 (∫r in (0:ℝ)..1,∫s in (0:ℝ)..1,K r s)) := by
  -- All meshes are integrated on the same actual rectangle; their moving cutoffs are finite data.
  let μ := volume.restrict (Ioo (0:ℝ) 1)
  let F (i:ι) (r s:ℝ) := a i (Nat.floor ((n i:ℝ)*r)) (Nat.floor ((n i:ℝ)*s))
  have hm (i:ι) (r:ℝ) : Measurable (F i r) :=
    (measurable_of_countable (a i (Nat.floor ((n i:ℝ)*r)))).comp
      (Nat.measurable_floor.comp (by fun_prop))
  have houter (i:ι) : Measurable (fun r:ℝ => ∫s in (0:ℝ)..1,F i r s) := by
    let g (j:ℕ) := ∫s in (0:ℝ)..1,a i j (Nat.floor ((n i:ℝ)*s))
    exact (measurable_of_countable g).comp (Nat.measurable_floor.comp (by fun_prop))
  have hpoint : ∀ᵐr ∂μ,Tendsto (fun i => ∫s in (0:ℝ)..1,F i r s) l
      (𝓝 (∫s in (0:ℝ)..1,K r s)) := by
    filter_upwards [hp] with r hr
    have h := tendsto_integral_filter_of_dominated_convergence (μ:=μ) (bound:=fun _ => B)
      (F:=fun i s => F i r s) (f:=K r)
      (Eventually.of_forall (fun i => (hm i r).aestronglyMeasurable))
      (hb.mono (fun i hi => Eventually.of_forall (fun s => hi _ _))) (integrable_const _) hr
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      ← restrict_Ioo_eq_restrict_Ioc,μ] using h
  have hbound : ∀ᶠi in l,∀r:ℝ,‖∫s in (0:ℝ)..1,F i r s‖≤B := by
    filter_upwards [hb] with i hi
    intro r
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(0:ℝ)) (b:=1) (f:=F i r) (C:=B) (fun s _ => hi _ _)
    simpa only [sub_zero,abs_one,mul_one] using h
  have hlimit := tendsto_integral_filter_of_dominated_convergence (μ:=μ) (bound:=fun _ => B)
    (F:=fun i r => ∫s in (0:ℝ)..1,F i r s) (f:=fun r => ∫s in (0:ℝ)..1,K r s)
    (Eventually.of_forall (fun i => (houter i).aestronglyMeasurable))
    (hbound.mono (fun i hi => Eventually.of_forall hi)) (integrable_const _) hpoint
  have hsum := hlimit.congr' (by
    filter_upwards [hn.eventually_gt_atTop 0] with i hi
    have h := double_mesh_integral (n i) (a i) hi
    simpa only [F,μ,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      ← restrict_Ioo_eq_restrict_Ioc] using h)
  simpa only [μ,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← restrict_Ioo_eq_restrict_Ioc] using hsum

end
end jacobi.Analysis
