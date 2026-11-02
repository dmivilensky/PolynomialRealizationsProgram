import jacobi.Fredholm.Moments

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
All original state quadratures and their two parameter-response moments
are jointly continuous on the closed physical parameter box. The singular
endpoints v=0,1 are null and have one common integrable majorant.
Source: dominated convergence for Lebesgue integrals, with the original weights retained.
Use: joint dominated continuity includes every endpoint needed by one-sided Fredholm calculus.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The closed physical parameter box for the common elliptic weights.
Use: joint dominated continuity includes every endpoint needed by one-sided Fredholm calculus.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def parameterBox : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1

/-- A uniformly dominated genuine family has joint continuous unit-interval integrals on the physical parameter box.
Use: proves continuity of original moments and response moments by the same analytic argument.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: apply dominated convergence on (0,1) with the verified endpoint
weight, then restore the identical interval integrals. The two null
endpoint representatives do not affect any actual integral. -/
theorem box_integral_continuous (F : (ℝ × ℝ) → ℝ → ℝ)
    (hm : ∀ p,Measurable (F p))
    (hb : ∀ p∈parameterBox,∀ v∈Ioo (0:ℝ) 1,|F p v|≤endpointWeight v)
    (hc : ∀ v∈Ioo (0:ℝ) 1,ContinuousOn (fun p => F p v) parameterBox) :
    ContinuousOn (fun p => ∫ v in (0:ℝ)..1,F p v) parameterBox := by
  -- The parameter set is retained exactly; no extension through a singular endpoint is asserted.
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp endpointWeight_integrable
  have H := MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (s := parameterBox) (F := F) (bound := endpointWeight)
    (fun p _ => (hm p).aestronglyMeasurable)
    (fun p hp => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      exact hb p hp v hv) hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      exact hc v hv)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo] using H

/-- Bounded fixed numerators preserve joint continuity of the actual original quadrature weight.
Use: a=1 and a=v give genuine continuity of i2 and i3 at every physical boundary.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the original measurable integrands have the common endpoint
majorant, and P is strictly positive at each interior coordinate. -/
theorem state_integral_continuous (a : ℝ → ℝ) (ha : Measurable a)
    (hB : ∀ v∈Ioo (0:ℝ) 1,|a v|≤1) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ v in (0:ℝ)..1,a v*quadratureWeight p.1 p.2 v) parameterBox := by
  -- Positivity of the true polynomial licenses pointwise continuity before dominated convergence.
  apply box_integral_continuous (fun p v => a v*quadratureWeight p.1 p.2 v)
    (fun p => ha.mul (by unfold quadratureWeight P r q; fun_prop))
    (fun p hp v hv => ?_) (fun v hv p hp => ?_)
  · have hw := quadratureWeight_bound hp.1 hp.2 hv
    rw [abs_mul,abs_of_nonneg hw.1]
    exact (mul_le_mul (hB v hv) hw.2 hw.1 (by norm_num)).trans_eq (one_mul _)
  · have hP : Continuous (fun q : ℝ × ℝ => P q.1 q.2 v) := by unfold P r q; fun_prop
    exact (continuousAt_const.mul (continuousAt_const.div
      (continuous_sqrt.continuousAt.comp hP.continuousAt)
      (sqrt_pos.mpr (P_pos hp.1 hp.2 hv)).ne')).continuousWithinAt

/-- Bounded fixed numerators preserve joint continuity of the genuine shape-derivative integral.
Use: both state shape derivatives have continuous physical boundary values at tau=1.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the original response is pointwise continuous because r and P
are positive, and its absolute value is uniformly bounded by the proved endpoint weight. -/
theorem shape_integral_continuous (a : ℝ → ℝ) (ha : Measurable a)
    (hB : ∀ v∈Ioo (0:ℝ) 1,|a v|≤1) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ v in (0:ℝ)..1,
      a v*(psi p.1 p.2 v*quadratureWeight p.1 p.2 v)) parameterBox := by
  -- The same uniform bound remains valid at both parameter endpoints.
  apply box_integral_continuous (fun p v => a v*(psi p.1 p.2 v*quadratureWeight p.1 p.2 v))
    (fun p => ha.mul (by unfold psi N L quadratureWeight P r q; fun_prop))
    (fun p hp v hv => ?_) (fun v hv p hp => ?_)
  · have hw := shapeWeight_bound hp.1 hp.2 hv
    rw [abs_mul,abs_of_nonneg hw.1]
    exact (mul_le_mul (hB v hv) hw.2 hw.1 (by norm_num)).trans_eq (one_mul _)
  · have hR := (r_pos hp.1 hp.2 ⟨hv.1,hv.2.le⟩).ne'
    have hS := (sqrt_pos.mpr (P_pos hp.1 hp.2 hv)).ne'
    apply ContinuousAt.continuousWithinAt
    unfold psi N L quadratureWeight P r q
    fun_prop (disch := first | exact hR | exact hS | positivity)

/-- Bounded fixed numerators preserve joint continuity of the genuine positive determinant-response integral.
Use: both chi derivatives have continuous physical endpoint values, including chi=0.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: h and the original weight are pointwise continuous inside the
integration interval; h<=1 and the common weight bound supply uniform domination. -/
theorem response_integral_continuous (a : ℝ → ℝ) (ha : Measurable a)
    (hB : ∀ v∈Ioo (0:ℝ) 1,|a v|≤1) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ v in (0:ℝ)..1,
      a v*((v^3/r p.1 p.2 v)*quadratureWeight p.1 p.2 v)) parameterBox := by
  -- Keep the response before its chi derivative coefficient, which can vanish at tau=0.
  apply box_integral_continuous (fun p v => a v*((v^3/r p.1 p.2 v)*quadratureWeight p.1 p.2 v))
    (fun p => ha.mul (by unfold quadratureWeight P r q; fun_prop))
    (fun p hp v hv => ?_) (fun v hv p hp => ?_)
  · have hh := h_bounds hp.1 hp.2 hv
    have hw := quadratureWeight_bound hp.1 hp.2 hv
    rw [abs_mul,abs_of_nonneg (mul_nonneg hh.1 hw.1)]
    have hb := (mul_le_mul (hh.2.trans hv.2.le) hw.2 hw.1 (by norm_num)).trans_eq (one_mul _)
    exact (mul_le_mul (hB v hv) hb (mul_nonneg hh.1 hw.1) (by norm_num)).trans_eq (one_mul _)
  · have hR := (r_pos hp.1 hp.2 ⟨hv.1,hv.2.le⟩).ne'
    have hS := (sqrt_pos.mpr (P_pos hp.1 hp.2 hv)).ne'
    apply ContinuousAt.continuousWithinAt
    unfold quadratureWeight P r q
    fun_prop (disch := first | exact hR | exact hS | positivity)

end
end jacobi.Fredholm
