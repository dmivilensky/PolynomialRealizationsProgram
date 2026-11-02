import chebyshev1.Analysis.StepIntegral
import chebyshev1.Analysis.MeshApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Floor

/-!
Article: jacobi, Theorem 2.1.
Source: dominated convergence for uniform Riemann sums.
Use: Support.topValue_square_norm_limit proves the genuine spectral weight normalization; the original support edge and Gram limits use the same mesh-to-integral passage.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory chebyshev1.Analysis
open scoped Topology

/-- Uniformly convergent actual finite mesh values have the continuous limit's integral as their normalized finite-sum limit.
Use: Support.topValue_square_norm_limit proves the genuine spectral weight normalization; the original support edge and Gram limits use the same mesh-to-integral passage.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: uniform Riemann sums and dominated convergence; exact cell integration and floor-mesh convergence are reused from chebyshev1.
Proof: represent each normalized sum by its exact original step integral. The old floor-mesh theorem and the given uniform convergence imply pointwise convergence inside the unit interval. Compact continuity and the uniform error at tolerance one supply a common integrable constant bound, so dominated convergence applies. -/
theorem uniform_mesh_integral (a : ℕ→ℕ→ℝ) (f : ℝ→ℝ) (hf:Continuous f)
    (ha:∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀j<n,|a n j-f ((j:ℝ)/(n:ℝ))|<ε) :
    Tendsto (fun n:ℕ => (∑j∈Finset.range n,a n j)/(n:ℝ)) atTop (𝓝 (∫t in (0:ℝ)..1,f t)) := by
  -- The same original floor cells are used for both the exact sum identity and the dominated limit.
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s:=Icc (0:ℝ) 1) hf.continuousOn
  obtain ⟨n₀,hn₀⟩ := ha 1 (by norm_num)
  have hpoint (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) :
      Tendsto (fun n:ℕ => uniformStep n (a n) t) atTop (𝓝 (f t)) := by
    have hmesh := floor_mesh_limit tendsto_id (tendsto_const_nhds (x:=t))
      (Eventually.of_forall (fun _ => ht.1.le))
    have herr : Tendsto (fun n:ℕ => uniformStep n (a n) t-f ((Nat.floor ((n:ℝ)*t):ℝ)/(n:ℝ))) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨N,hN⟩ := ha ε hε
      filter_upwards [eventually_ge_atTop N,eventually_gt_atTop (0:ℕ)] with n hn hnpos
      simpa only [uniformStep,Real.norm_eq_abs,Real.dist_eq,sub_zero] using
        hN n hn _ (floor_unit_bounds n hnpos ht).1
    have h := herr.add (hf.continuousAt.tendsto.comp hmesh)
    simpa only [Function.comp_def,id_eq,sub_add_cancel,zero_add] using h
  have hlimit := tendsto_integral_filter_of_dominated_convergence
    (μ:=volume.restrict (Ioo (0:ℝ) 1)) (bound:=fun _ => C+1)
    (F:=fun n t => uniformStep n (a n) t) (f:=f)
    (Eventually.of_forall (fun n => by
      apply Measurable.aestronglyMeasurable
      exact (measurable_of_countable (a n)).comp (Nat.measurable_floor.comp (by fun_prop))))
    (by
      filter_upwards [eventually_ge_atTop n₀,eventually_gt_atTop (0:ℕ)] with n hn hnpos
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hk := floor_unit_bounds n hnpos ht
      have hnreal : (0:ℝ)<n := by exact_mod_cast hnpos
      have hratio : (Nat.floor ((n:ℝ)*t):ℝ)/(n:ℝ)∈Icc (0:ℝ) 1 := by
        refine ⟨by positivity,?_⟩
        apply (div_le_one hnreal).mpr
        exact_mod_cast hk.1.le
      have hnorm := norm_add_le (a n (Nat.floor ((n:ℝ)*t))-f ((Nat.floor ((n:ℝ)*t):ℝ)/(n:ℝ)))
        (f ((Nat.floor ((n:ℝ)*t):ℝ)/(n:ℝ)))
      have herr := hn₀ n hn _ hk.1
      have hval := hC _ hratio
      simp only [sub_add_cancel,Real.norm_eq_abs] at hnorm
      change |a n (Nat.floor ((n:ℝ)*t))|≤C+1
      exact hnorm.trans (by simpa only [Real.norm_eq_abs,add_comm C 1] using add_le_add herr.le hval))
    (integrable_const _)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht; exact hpoint t ht)
  have hsum := hlimit.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have h := uniformStep_integral n (a n) hn
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      restrict_Ioo_eq_restrict_Ioc] using h)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    restrict_Ioo_eq_restrict_Ioc] using hsum

end
end jacobi.Analysis
