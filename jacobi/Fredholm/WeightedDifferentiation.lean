import jacobi.Fredholm.DominatedQuadrature

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Differentiation of an endpoint-singular integral reduces to continuity
on a compact rectangle after removing the common square-root weight.
Source: differentiation under the integral sign with an integrable
dominating function, using mathlib's parametric integral theorem.
Use: differentiates the original Green core in the Fredholm envelope identity; compactness supplies a bound without introducing numerical estimates.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Compact continuous coefficients of the common endpoint weight admit genuine integral differentiation.
Use: differentiates the original Green core in the Fredholm envelope identity;
compactness supplies a bound without introducing numerical estimates.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: bound the coefficient derivative on the compact parameter-coordinate
rectangle. Multiply this bound by the integrable endpoint weight and apply
dominated differentiation on the open parameter interval. -/
theorem compact_weight_hasDerivAt (F D : ℝ → ℝ → ℝ)
    (hFm : ∀ u,Measurable (F u)) (hDm : ∀ u,Measurable (D u))
    {a b u : ℝ} (hu : u∈Ioo a b)
    (hF : ContinuousOn (F u) (Icc (0:ℝ) 1))
    (hD : ContinuousOn (fun p : ℝ×ℝ => D p.1 p.2) (Icc a b×ˢIcc (0:ℝ) 1))
    (hd : ∀ x∈Ioo a b,∀ v∈Ioo (0:ℝ) 1,HasDerivAt (fun y => F y v) (D x v) x) :
    IntervalIntegrable (fun v => D u v*endpointWeight v) volume 0 1 ∧
      HasDerivAt (fun x => ∫ v in (0:ℝ)..1,F x v*endpointWeight v)
        (∫ v in (0:ℝ)..1,D u v*endpointWeight v) u := by
  -- The only singular factor is independent of the differentiated parameter.
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hD
  have hm : Measurable endpointWeight := by unfold endpointWeight; fun_prop
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp
    endpointWeight_integrable
  have hFi : Integrable (fun v => F u v*endpointWeight v) (volume.restrict (Ioo (0:ℝ) 1)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp
    exact endpointWeight_integrable.continuousOn_mul (by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hF)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (s := Ioo a b)
    (F := fun x v => F x v*endpointWeight v)
    (F' := fun x v => D x v*endpointWeight v) (bound := fun v => C*endpointWeight v)
    (isOpen_Ioo.mem_nhds hu)
    (Eventually.of_forall fun x => ((hFm x).mul hm).aestronglyMeasurable) hFi
    ((hDm u).mul hm).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro x hx
      rw [norm_mul,Real.norm_of_nonneg (show 0≤endpointWeight v by unfold endpointWeight; positivity)]
      exact mul_le_mul_of_nonneg_right (hC (x,v) ⟨⟨hx.1.le,hx.2.le⟩,⟨hv.1.le,hv.2.le⟩⟩)
        (by unfold endpointWeight; positivity))
    (hi.const_mul C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro x hx
      exact (hd x hx v hv).mul_const (endpointWeight v))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr h.1,?_⟩
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_Ioc_eq_integral_Ioo] using h.2

end
end jacobi.Fredholm
