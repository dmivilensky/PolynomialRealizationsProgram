import jacobi.Fredholm.DerivativeBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
A common dominated differentiation argument handles both parameters of the
original singular state integrals, retaining their actual unit interval.
The uniform weight and derivative majorants are proved in DerivativeBounds.
Source: mathlib's dominated parameter differentiation of Lebesgue integrals.
Use: one analytic argument serves both actual Fredholm derivatives without repeating endpoint analysis.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Uniformly dominated positive weights have genuine integral derivatives for every bounded measurable numerator.
Use: one analytic argument serves both actual Fredholm derivatives without repeating endpoint analysis.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: the original integrand and its derivative share the proved
integrable endpoint majorant. Apply dominated differentiation on the open
parameter interval, then restore the equal genuine interval integral. -/
theorem bounded_weight_hasDerivAt (W D : ℝ → ℝ → ℝ)
    (hWm : ∀ u,Measurable (W u)) (hDm : ∀ u,Measurable (D u))
    (hW : ∀ u∈Icc (0:ℝ) 1,∀ v∈Ioo (0:ℝ) 1,0≤W u v ∧ W u v≤endpointWeight v)
    (hD : ∀ u∈Icc (0:ℝ) 1,∀ v∈Ioo (0:ℝ) 1,|D u v|≤endpointWeight v)
    (hder : ∀ u∈Icc (0:ℝ) 1,∀ v∈Ioo (0:ℝ) 1,HasDerivAt (fun a => W a v) (D u v) u)
    (a : ℝ → ℝ) (ha : Measurable a) (haB : ∀ v∈Ioo (0:ℝ) 1,|a v|≤1)
    {u : ℝ} (hu : u∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (fun v => a v*D u v) volume 0 1 ∧
      HasDerivAt (fun b => ∫ v in (0:ℝ)..1,a v*W b v)
        (∫ v in (0:ℝ)..1,a v*D u v) u := by
  -- Remove the two null endpoints uniformly before invoking dominated differentiation.
  have hBi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp endpointWeight_integrable
  have hm (b : ℝ) : AEStronglyMeasurable (fun v => a v*W b v) (volume.restrict (Ioo (0:ℝ) 1)) :=
    (ha.mul (hWm b)).aestronglyMeasurable
  have hboundW (b : ℝ) (hb : b∈Icc (0:ℝ) 1) : ∀ᵐ v ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖a v*W b v‖≤endpointWeight v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hW b hb v hv).1]
    exact (mul_le_mul (haB v hv) (hW b hb v hv).2 (hW b hb v hv).1 (by norm_num)).trans_eq (one_mul _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (s := Ioo (0:ℝ) 1)
    (F := fun b v => a v*W b v) (F' := fun b v => a v*D b v) (bound := endpointWeight)
    (isOpen_Ioo.mem_nhds hu) (Eventually.of_forall hm)
    (hBi.mono' (hm u) (hboundW u ⟨hu.1.le,hu.2.le⟩))
    (ha.mul (hDm u)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro b hb
      rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul (haB v hv) (hD b ⟨hb.1.le,hb.2.le⟩ v hv)
        (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)) hBi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro b hb
      exact (hder b ⟨hb.1.le,hb.2.le⟩ v hv).const_mul (a v))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr h.1,?_⟩
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo] using h.2

/-- Every bounded measurable numerator has its genuine interior shape derivative under the actual Fredholm weight.
Use: a=1 and a=v give the two derivatives required by the shape-ratio monotonicity proof.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: apply the common dominated theorem to the actual weight and its
verified psi derivative, with the uniform endpoint bounds discharged. -/
theorem shape_quadrature_hasDerivAt {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1)
    (a : ℝ → ℝ) (ha : Measurable a) (haB : ∀ v∈Ioo (0:ℝ) 1,|a v|≤1) :
    IntervalIntegrable (fun v => a v*(psi t c v*quadratureWeight t c v)) volume 0 1 ∧
      HasDerivAt (fun u => ∫ v in (0:ℝ)..1,a v*quadratureWeight u c v)
        (∫ v in (0:ℝ)..1,a v*(psi t c v*quadratureWeight t c v)) t := by
  -- Every physical pointwise derivative concerns the original weight, including near v=0.
  apply bounded_weight_hasDerivAt (fun u v => quadratureWeight u c v)
    (fun u v => psi u c v*quadratureWeight u c v)
    (fun _ => by unfold quadratureWeight P r q; fun_prop)
    (fun _ => by unfold psi N L quadratureWeight P r q; fun_prop)
    (fun u hu v hv => quadratureWeight_bound hu hc hv)
    (fun u hu v hv => by rw [abs_of_nonneg (shapeWeight_bound hu hc hv).1]; exact (shapeWeight_bound hu hc hv).2)
    (fun u hu v hv => ?_) a ha haB ht
  convert (inverse_sqrt_shape_hasDerivAt hu hc hv).const_mul (v^2) using 1 <;>
    (try funext b) <;> (unfold quadratureWeight; ring)

/-- Every bounded measurable numerator has its genuine determinant-parameter derivative, including full support.
Use: a=1 and a=v give both chi derivatives at every physical shape tau in [0,1].
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: apply the common dominated theorem to the original weight and
its verified inverse-square-root chi derivative, with uniform bounds. -/
theorem parameter_quadrature_hasDerivAt {t c : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1)
    (a : ℝ → ℝ) (ha : Measurable a) (haB : ∀ v∈Ioo (0:ℝ) 1,|a v|≤1) :
    IntervalIntegrable (fun v => a v*(-(t/2)*(v^3/r t c v)*quadratureWeight t c v)) volume 0 1 ∧
      HasDerivAt (fun u => ∫ v in (0:ℝ)..1,a v*quadratureWeight t u v)
        (∫ v in (0:ℝ)..1,a v*(-(t/2)*(v^3/r t c v)*quadratureWeight t c v)) c := by
  -- At tau=1 only chi varies, so the derivative remains an ordinary interior real derivative.
  apply bounded_weight_hasDerivAt (fun u v => quadratureWeight t u v)
    (fun u v => -(t/2)*(v^3/r t u v)*quadratureWeight t u v)
    (fun _ => by unfold quadratureWeight P r q; fun_prop)
    (fun _ => by unfold quadratureWeight P r q; fun_prop)
    (fun u hu v hv => quadratureWeight_bound ht hu hv)
    (fun u hu v hv => parameterWeight_bound ht hu hv)
    (fun u hu v hv => ?_) a ha haB hc
  convert (inverse_sqrt_fredholm_hasDerivAt ht hu hv).const_mul (v^2) using 1 <;>
    (try funext b) <;> (unfold quadratureWeight; ring)

end
end jacobi.Fredholm
