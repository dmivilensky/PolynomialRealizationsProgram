import jacobi.Fredholm.DominatedQuadrature

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The four auxiliary moments are the genuine derivatives of i2 and i3.
Their convergence is proved uniformly on the physical box. In particular,
the determinant-parameter derivatives remain ordinary derivatives at tau=1.
Source: the common dominated quadrature theorem and verified weight derivatives.
Use: the mass shape derivative and the decreasing shape-ratio comparison.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The actual second shape-derivative moment.
Use: the mass shape derivative and the decreasing shape-ratio comparison.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def shape2 (t c : ℝ) : ℝ := ∫ v in (0:ℝ)..1,psi t c v*quadratureWeight t c v

/-- The actual third shape-derivative moment.
Use: the objective shape derivative and Chebyshev's integral inequality.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def shape3 (t c : ℝ) : ℝ := ∫ v in (0:ℝ)..1,v*(psi t c v*quadratureWeight t c v)

/-- The positive second determinant-response moment before its derivative coefficient.
Use: the mass parameter derivative and its strict sign.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def response2 (t c : ℝ) : ℝ := ∫ v in (0:ℝ)..1,(v^3/r t c v)*quadratureWeight t c v

/-- The positive third determinant-response moment before its derivative coefficient.
Use: the nonnegative determinant-parameter derivative of the energy-to-mass ratio.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
-/
def response3 (t c : ℝ) : ℝ := ∫ v in (0:ℝ)..1,v*((v^3/r t c v)*quadratureWeight t c v)

/-- A measurable integrand bounded by the actual endpoint weight has its genuine finite interval integral.
Use: proves convergence of each original auxiliary moment before any integral algebra.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: use the integrable endpoint majorant on (0,1); the two endpoint representatives are null. -/
theorem endpoint_integrable (f : ℝ → ℝ) (hm : Measurable f)
    (hb : ∀ v∈Ioo (0:ℝ) 1,|f v|≤endpointWeight v) : IntervalIntegrable f volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp endpointWeight_integrable).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  exact hb v hv

/-- Both true shape-response integrands are integrable throughout the closed physical box.
Use: justifies the covariance expansion and normalized derivative comparisons.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: dominate the second response by the common endpoint weight and
multiply by the continuous bounded coordinate for the third response. -/
theorem shape_integrable {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    IntervalIntegrable (fun v => psi t c v*quadratureWeight t c v) volume 0 1 ∧
      IntervalIntegrable (fun v => v*(psi t c v*quadratureWeight t c v)) volume 0 1 := by
  have hi := endpoint_integrable (fun v => psi t c v*quadratureWeight t c v)
    (by unfold psi N L quadratureWeight P r q; fun_prop)
    (fun v hv => by rw [abs_of_nonneg (shapeWeight_bound ht hc hv).1]; exact (shapeWeight_bound ht hc hv).2)
  exact ⟨hi,hi.continuousOn_mul continuous_id.continuousOn⟩

/-- Both positive determinant-response integrands converge throughout the closed physical box.
Use: permits positive-mean comparisons independently of a nonzero derivative coefficient.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: h lies between zero and one, so its second response is dominated
by the common original weight; multiplication by the coordinate gives the third. -/
theorem response_integrable {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    IntervalIntegrable (fun v => (v^3/r t c v)*quadratureWeight t c v) volume 0 1 ∧
      IntervalIntegrable (fun v => v*((v^3/r t c v)*quadratureWeight t c v)) volume 0 1 := by
  -- This domination also works at tau=0, where the determinant derivative coefficient vanishes.
  have hi := endpoint_integrable (fun v => (v^3/r t c v)*quadratureWeight t c v)
    (by unfold quadratureWeight P r q; fun_prop) (fun v hv => by
      have hh := h_bounds ht hc hv
      have hw := quadratureWeight_bound ht hc hv
      rw [abs_of_nonneg (mul_nonneg hh.1 hw.1)]
      exact (mul_le_mul (hh.2.trans hv.2.le) hw.2 hw.1 (by norm_num)).trans_eq (one_mul _))
  exact ⟨hi,hi.continuousOn_mul continuous_id.continuousOn⟩

/-- Both original state moments have their genuine interior shape derivatives.
Use: differentiates the literal mass and energy, and their normalized shape ratio.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: specialize the common dominated differentiation theorem to the
bounded numerators one and v respectively. -/
theorem shape_calculus {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    HasDerivAt (fun u => i2 u c) (shape2 t c) t ∧
      HasDerivAt (fun u => i3 u c) (shape3 t c) t := by
  constructor
  · simpa only [i2,shape2,one_mul] using (shape_quadrature_hasDerivAt ht hc (fun _ => 1)
      measurable_const (fun _ _ => by norm_num)).2
  · exact (shape_quadrature_hasDerivAt ht hc (fun v => v) measurable_id
      (fun v hv => by rw [abs_of_pos hv.1]; exact hv.2.le)).2

/-- Both original state moments have their genuine determinant-parameter derivatives, including the full-support shape.
Use: differentiates the actual free-branch objective and the energy-to-mass ratio.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: specialize dominated differentiation to one and v, then pull the
constant negative derivative coefficient out of the actual convergent integral. -/
theorem parameter_calculus {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => i2 t u) (-(t/2)*response2 t c) c ∧
      HasDerivAt (fun u => i3 t u) (-(t/2)*response3 t c) c := by
  -- The coefficient is moved only after obtaining the genuine integral derivative.
  have h2 := (parameter_quadrature_hasDerivAt ht hc (fun _ => 1) measurable_const (fun _ _ => by norm_num)).2
  have h3 := (parameter_quadrature_hasDerivAt ht hc (fun v => v) measurable_id
    (fun v hv => by rw [abs_of_pos hv.1]; exact hv.2.le)).2
  norm_num only [one_mul] at h2
  have he2 : (∫ v in (0:ℝ)..1,-(t/2)*(v^3/r t c v)*quadratureWeight t c v)=-(t/2)*response2 t c := by
    unfold response2
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext v
    ring
  have he3 : (∫ v in (0:ℝ)..1,v*(-(t/2)*(v^3/r t c v)*quadratureWeight t c v))=-(t/2)*response3 t c := by
    unfold response3
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext v
    ring
  exact ⟨he2 ▸ h2,he3 ▸ h3⟩

end
end jacobi.Fredholm
