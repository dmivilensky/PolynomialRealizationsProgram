import jacobi.Analysis.UniformMeshIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Exact complex mesh integration reuses the real step-integral theorem
from chebyshev1. The complex form and its iterated version turn the
actual finite ground-normalized Volterra sums into ordinary integrals.
Source: integration of finite step functions and real-linear projections.
Use: complex_mesh_integral commutes integration with real and imaginary projections with genuine integrability; double_mesh_integral then integrates both original finite mesh indices.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter MeasureTheory chebyshev1.Analysis
open scoped Topology

/-- Every actual complex mesh function is integrable on its unit interval.
Use: complex_mesh_integral commutes integration with real and imaginary projections with genuine integrability; double_mesh_integral then integrates both original finite mesh indices.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: bounded measurable functions on a finite measure space.
Proof: the original floor index belongs to the finite mesh range almost everywhere. The sum of the norms of its finitely many values is a constant integrable majorant. -/
theorem complex_mesh_integrable (N : ℕ) (a : ℕ→ℂ) (hN : 0<N) :
    IntervalIntegrable (fun t:ℝ => a (Nat.floor ((N:ℝ)*t))) volume 0 1 := by
  -- Only the actual used finite mesh range needs a bound.
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr
  apply (integrable_const (∑j∈Finset.range N,‖a j‖)).mono'
    (((measurable_of_countable a).comp (Nat.measurable_floor.comp (by fun_prop))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with t ht hne
  have hk := floor_unit_bounds N hN ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  exact Finset.single_le_sum (fun j _ => norm_nonneg (a j)) (Finset.mem_range.mpr hk.1)

/-- The exact original finite complex mesh sum equals its step integral.
Use: double_mesh_integral represents the ground-normalized finite Volterra operator by two bounded mesh integrals, allowing a direct continuum limit at complex energy.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: chebyshev1, Analysis.uniformStep_integral, applied to the two real-linear coordinates.
Proof: commute the real and imaginary projections with the genuinely integrable complex step function. The existing real mesh theorem computes each projected integral and each projected finite sum exactly. -/
theorem complex_mesh_integral (N : ℕ) (a : ℕ→ℂ) (hN : 0<N) :
    (∫t in (0:ℝ)..1,a (Nat.floor ((N:ℝ)*t)))=(∑j∈Finset.range N,a j)/(N:ℂ) := by
  -- Reuse the first article's exact real mesh integration for both coordinates.
  have hi := complex_mesh_integrable N a hN
  apply Complex.ext
  · have h := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫t in (0:ℝ)..1,(a (Nat.floor ((N:ℝ)*t))).re)=
      (∫t in (0:ℝ)..1,a (Nat.floor ((N:ℝ)*t))).re at h
    rw [← h]
    change _=((∑j∈Finset.range N,a j)/((N:ℝ):ℂ)).re
    rw [Complex.div_ofReal_re]
    have hs : (∑j∈Finset.range N,a j).re=∑j∈Finset.range N,(a j).re :=
      map_sum Complex.reCLM _ _
    rw [hs]
    simpa only [uniformStep] using
      uniformStep_integral N (fun j => (a j).re) hN
  · have h := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫t in (0:ℝ)..1,(a (Nat.floor ((N:ℝ)*t))).im)=
      (∫t in (0:ℝ)..1,a (Nat.floor ((N:ℝ)*t))).im at h
    rw [← h]
    change _=((∑j∈Finset.range N,a j)/((N:ℝ):ℂ)).im
    rw [Complex.div_ofReal_im]
    have hs : (∑j∈Finset.range N,a j).im=∑j∈Finset.range N,(a j).im :=
      map_sum Complex.imCLM _ _
    rw [hs]
    simpa only [uniformStep] using
      uniformStep_integral N (fun j => (a j).im) hN

/-- Two exact complex mesh integrations give the original normalized finite double sum.
Use: the ground-normalized finite Volterra operator has a bounded two-variable step representation on one fixed rectangle, including its triangular index cutoffs.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: integrate the inner original mesh exactly, move its constant degree denominator through the outer integral, and integrate the remaining finite mesh exactly once more. -/
theorem double_mesh_integral (N : ℕ) (a : ℕ→ℕ→ℂ) (hN : 0<N) :
    (∫r in (0:ℝ)..1,∫s in (0:ℝ)..1,
      a (Nat.floor ((N:ℝ)*r)) (Nat.floor ((N:ℝ)*s)))=
      (∑l∈Finset.range N,∑j∈Finset.range N,a l j)/(N:ℂ)^2 := by
  -- The index cutoffs are part of the actual finite data; no continuity of that step data is needed.
  simp_rw [complex_mesh_integral N _ hN]
  rw [intervalIntegral.integral_div]
  rw [complex_mesh_integral N (fun l => ∑j∈Finset.range N,a l j) hN]
  ring

end
end jacobi.Analysis
