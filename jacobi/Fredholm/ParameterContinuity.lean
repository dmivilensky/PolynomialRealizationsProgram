import jacobi.Fredholm.ParameterUniqueness

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The original determinant is continuous up to full support at fixed
physical chi. Its original core integrand has a common integrable bound,
so no differentiable extension through tau=1 is used.
Source: dominated convergence and the verified Green weight bound.
Use: brackets mass roots and compares the interior and free Fredholm alternatives.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal mass is continuous in shape on the complete closed physical interval.
Use: brackets mass roots and compares the interior and free Fredholm alternatives.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: restrict the proved joint dominated second-moment continuity
to the fixed physical chi line and multiply by its constant normalization. -/
theorem mass_shape_continuous {c : ℝ} (hc : c∈Icc (0:ℝ) 1) :
    ContinuousOn (fun t => mass t c) (Icc (0:ℝ) 1) := by
  have hI : ContinuousOn (fun p : ℝ×ℝ => i2 p.1 p.2) parameterBox := by
    simpa only [i2,one_mul] using state_integral_continuous (fun _ => 1)
      measurable_const (fun _ _ => by norm_num)
  exact (hI.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht,hc⟩)).const_mul ((3/2:ℝ)*c)

/-- The actual mass is continuous in chi on its entire closed physical interval.
Use: the intermediate value theorem constructs genuine mass roots strictly below chi=1.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: restrict the proved joint second-moment continuity to fixed tau
and multiply by the continuous chi normalization. -/
theorem mass_parameter_continuous {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ContinuousOn (mass t) (Icc (0:ℝ) 1) := by
  -- Restrict the original jointly continuous moment before applying the varying chi normalization.
  have hI : ContinuousOn (fun p : ℝ×ℝ => i2 p.1 p.2) parameterBox := by
    simpa only [i2,one_mul] using state_integral_continuous (fun _ => 1)
      measurable_const (fun _ _ => by norm_num)
  have hmap : ContinuousOn (fun c : ℝ => (t,c)) (Icc (0:ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hraw := hI.comp hmap (fun _ hc => ⟨ht,hc⟩)
  have hIc : ContinuousOn (fun c => i2 t c) (Icc (0:ℝ) 1) := hraw
  change ContinuousOn (fun c => (3/2:ℝ)*c*i2 t c) (Icc (0:ℝ) 1)
  exact (continuousOn_const.mul continuousOn_id).mul hIc

/-- The original Green core integral is continuous through the full-support endpoint at fixed physical chi.
Use: joins the true determinant values of the two calibration branches.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: the original measurable integrand is bounded by the proved
(1-chi)^(-1) endpoint majorant on the full closed shape interval.
Its denominator is positive at every interior coordinate. Apply dominated
convergence and restore the identical original interval integral. -/
theorem core_shape_continuous {c : ℝ} (hc : c∈Ico (0:ℝ) 1) :
    ContinuousOn (fun t => ∫ v in (0:ℝ)..1,determinantWeight t c v) (Icc (0:ℝ) 1) := by
  -- Dominating the original integrand avoids a false positive lower bound for r at tau=1,v=0.
  have hi := ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp
    endpointWeight_integrable).const_mul ((1-c)⁻¹)
  have h := MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (s := Icc (0:ℝ) 1)
    (F := fun t v => determinantWeight t c v) (bound := fun v => (1-c)⁻¹*endpointWeight v)
    (fun _ _ => (show Measurable (determinantWeight _ c) by
      unfold determinantWeight L nu P r q; fun_prop).aestronglyMeasurable)
    (fun t ht => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (determinantWeight_bound ht hc hv).1]
      exact (determinantWeight_bound ht hc hv).2) hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro t ht
      have hN := nu_bounds ht hc ⟨hv.1.le,hv.2.le⟩
      have hN0 : 0<1-c*t*(1-v) := hN.1.trans_le hN.2.1
      have hP := P_pos ht ⟨hc.1,hc.2.le⟩ hv
      apply ContinuousAt.continuousWithinAt
      unfold determinantWeight L nu P r q at *
      fun_prop (disch := positivity))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_Ioc_eq_integral_Ioo] using h

/-- The actual determinant is continuous on the entire closed shape interval, including full support.
Use: transfers strict interior mass-curve comparisons to the free-branch endpoint.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: the original core and mass quadratures are continuous. The
literal logarithm ratio is positive throughout the physical interval;
elementary continuity therefore combines all three original terms. -/
theorem determinant_shape_continuous {c : ℝ} (hc : c∈Ico (0:ℝ) 1) :
    ContinuousOn (fun t => determinant t c) (Icc (0:ℝ) 1) := by
  -- The logarithm is evaluated only at its actual positive physical argument.
  have hcore := core_shape_continuous hc
  have hmass := mass_shape_continuous ⟨hc.1,hc.2.le⟩
  have hlog : ContinuousOn (fun t => log ((1-c*t)/(1-c))) (Icc (0:ℝ) 1) := by
    intro t ht
    have hc1 := sub_pos.mpr hc.2
    have hnum : 0<1-c*t := by nlinarith [hc.2,mul_le_mul_of_nonneg_left ht.2 hc.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  exact (hlog.add ((continuousOn_id.mul continuousOn_const).mul hcore)).sub hmass

end
end jacobi.Fredholm
