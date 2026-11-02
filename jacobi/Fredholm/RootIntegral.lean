import jacobi.Fredholm.StateIntegrals

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The normalized first-power integral converges through the full-support
endpoint. Its strictly positive value computes the actual optimizing root
integral, so convergence of that original whole-line function is proved
before converting its root mass to an extended value.
Source: the common P lower bound and the true optimizing Jacobian.
Use: controls root mass and both parameter derivatives of the higher state quadratures.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The first-power normalized weight has a positive parameter-uniform endpoint majorant.
Use: controls root mass and both parameter derivatives of the higher state quadratures.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: the common bound P>=(1-v)*v² gives sqrt(P)>=v*sqrt(1-v);
all factors are strictly positive on the actual open integration interval. -/
theorem rootWeight_bound {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (hv : v∈Ioo (0:ℝ) 1) :
    0≤v/sqrt (P t c v) ∧ v/sqrt (P t c v)≤endpointWeight v := by
  have hs := sqrt_pos.mpr (P_pos ht hc hv)
  have he := sqrt_pos.mpr (sub_pos.mpr hv.2)
  have hb := sqrt_le_sqrt (P_bounds ht hc ⟨hv.1.le,hv.2.le⟩).1
  rw [sqrt_mul (sub_nonneg.mpr hv.2.le),sqrt_sq hv.1.le] at hb
  refine ⟨div_nonneg hv.1.le hs.le,?_⟩
  unfold endpointWeight
  exact (div_le_iff₀ hs).mpr ((le_inv_mul_iff₀ he).mpr (by nlinarith [hb]))

/-- The first-power normalized Green quadrature is a genuine finite positive integral throughout the physical parameter box.
Use: proves actual root convergence and prevents a junk integral from supplying the root formula.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: the original measurable integrand is dominated by the proved
integrable endpoint weight. Its pointwise positivity throughout (0,1)
then gives strict positivity of its genuine interval integral. -/
theorem rootWeight_integral {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    IntervalIntegrable (fun v => v/sqrt (P t c v)) volume 0 1 ∧
      0<(∫ v in (0:ℝ)..1,v/sqrt (P t c v)) := by
  -- The original untruncated integrand is retained at the degenerate full-support endpoint.
  have hi : IntervalIntegrable (fun v => v/sqrt (P t c v)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr
    have hm : Measurable (fun v : ℝ => v/sqrt (P t c v)) := by unfold P r q; fun_prop
    apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp endpointWeight_integrable).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (rootWeight_bound ht hc hv).1]
    exact (rootWeight_bound ht hc hv).2
  exact ⟨hi,intervalIntegral.intervalIntegral_pos_of_pos_on hi
    (fun v hv => div_pos hv.1 (sqrt_pos.mpr (P_pos ht hc hv))) (by norm_num)⟩

/-- The genuine optimizing root integral converges and equals the literal printed normalized root quadrature.
Use: supplies the final state integral in Lemma quad without an extra root-integrability premise.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: take the true square root of the normalized positive-part-square
density and apply the original first-power coordinate substitution. The
computed integral is strictly positive, hence the original function is
integrable. Positive square-root algebra gives its exact printed scale. -/
theorem Optimizer.root_quadrature {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    Integrable (fun x => sqrt (P.density.value x)) ∧
      sqrt (2*s)*(∫ x,sqrt (P.density.value x))=root (P.tau hs) (P.chi hs) := by
  -- Strict positivity of the actual first-power quadrature certifies convergence of the original whole-line root.
  have hp := P.parameters hs
  have ht := hp.1.1
  have hc := hp.2.1
  have hC : 0<3*P.chi hs/(2*s*P.tau hs) := by positivity
  have hI := rootWeight_integral ⟨ht.le,hp.1.2⟩ ⟨hc.le,hp.2.2.le⟩
  have he : (∫ x,sqrt (P.density.value x))=
      sqrt (3*P.chi hs/(2*s*P.tau hs))*P.tau hs*
        (∫ v in (0:ℝ)..1,v/sqrt (jacobi.Elliptic.P (P.tau hs) (P.chi hs) v)) := by
    have hpoint (x : ℝ) : sqrt (P.density.value x)=
        sqrt (3*P.chi hs/(2*s*P.tau hs))*max (P.coordinate hs x) 0 := by
      rw [P.normalized_density hs x,sqrt_mul hC.le,sqrt_sq (le_max_right _ _)]
    simp_rw [hpoint]
    rw [integral_const_mul]
    have hh := P.power_quadrature hs 1 (by decide)
    simp only [pow_one] at hh
    rw [hh]
    ring
  refine ⟨Integrable.of_integral_ne_zero (by rw [he]; exact (mul_pos
    (mul_pos (sqrt_pos.mpr hC) ht) hI.2).ne'),?_⟩
  have hst := sq_sqrt ht.le
  have hs0 : 0<sqrt (2*s) := sqrt_pos.mpr (by positivity)
  have ht0 : 0<sqrt (P.tau hs) := sqrt_pos.mpr ht
  rw [he,root,sqrt_div (by positivity : 0≤3*P.chi hs),sqrt_mul (by positivity : 0≤2*s),
    sqrt_mul (by positivity : 0≤3*P.chi hs)]
  field_simp [hs0.ne',ht0.ne']
  rw [hst]

end
end jacobi.Fredholm
