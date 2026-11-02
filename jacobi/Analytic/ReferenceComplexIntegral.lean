import jacobi.Analytic.ComplexPowerIntegral
import jacobi.Analytic.ReferenceNormIntegral
import jacobi.Reference.PositiveIntegral

/-!
Article: jacobi, Lemma C.1.
The original endpoint-singular sine integral converges and is holomorphic
in the complex exponent. Its continuous compact-domain part is integrated
against a fixed finite weighted measure; the singular endpoint power is
never treated as a continuous function. The exact complex beta integral
is identified with the actual continued Gauss wave.
Source: holomorphic parameter integration and the analytic identity theorem.
Use: the singular exponent is absorbed into a fixed finite measure in complex_sine_integral_holomorphic.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set MeasureTheory Filter
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal nonnegative sine-product base on the compact physical integration interval.
Use: the singular exponent is absorbed into a fixed finite measure in complex_sine_integral_holomorphic.
Article: jacobi, Lemma C.1.
-/
def sineBase (t:ℝ) : C(Icc (0:ℝ) t,ℝ) :=
  ⟨fun s => Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2,by fun_prop⟩

/-- The actual sine-product base is nonnegative on the full physical interval.
Use: applies the compact-domain complex-power construction including its zero endpoints.
Article: jacobi, Lemma C.1.
Proof: specialize the proved real sine-power positivity to exponent one. -/
theorem sineBase_product_nonneg {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (s:Icc (0:ℝ) t) : 0≤sineBase t s := by
  simpa only [sineBase,ContinuousMap.coe_mk,jacobi.Reference.sineWeight,show (2:ℝ)-1=1 by norm_num,Real.rpow_one] using
    jacobi.Reference.sineWeight_nonneg 2 ht s.property

/-- The literal integrand of the defining sine/beta integral at complex exponent and frequency.
Use: complex_sine_integral_holomorphic proves its genuine convergence and complex betaWave identifies its normalized integral with the original wave.
Article: jacobi, Lemma C.1.
-/
def complexSineIntegrand (g:ℂ) (t:ℝ) (omega:ℂ) (s:ℝ) : ℂ :=
  ((Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2:ℝ):ℂ)^(g-1)*
    Complex.cos (((t-2*s:ℝ):ℂ)*omega)

/-- The genuine original singular sine integral converges absolutely and is holomorphic in every admissible complex exponent.
Use: verifies that the analytic reference function is represented by the actual defining integral at nonreal orders, rather than only its real restriction.
Article: jacobi, Lemma C.1.
Proof: on the compact original interval the sine base is nonnegative and almost everywhere positive. Every required smaller endpoint power is integrable by the already proved real beta convergence. Apply the fixed weighted-measure holomorphy theorem and return from the compact subtype to the actual interval integral. -/
theorem complex_sine_integral_holomorphic {g:ℂ} (hg:0<g.re) {t:ℝ}
    (ht:t∈Ioo (0:ℝ) 1) (omega:ℂ) :
    IntervalIntegrable (complexSineIntegrand g t omega) volume 0 t ∧
      DifferentiableAt ℂ (fun z:ℂ => ∫ s in (0:ℝ)..t,complexSineIntegrand z t omega s) g := by
  -- Only the true zero endpoints are null; the original singular integrand is retained throughout the interior.
  let H : C(Icc (0:ℝ) t,ℂ) := ⟨fun s => Complex.cos (((t-2*s:ℝ):ℂ)*omega),by fun_prop⟩
  have hpos : ∀ᵐ s:Icc (0:ℝ) t,0<sineBase t s := by
    change ∀ᵐ s:Icc (0:ℝ) t ∂Measure.comap Subtype.val (volume:Measure ℝ),
      0<Real.sin (Real.pi*(s:ℝ))*Real.sin (Real.pi*(t-(s:ℝ)))/Real.pi^2
    apply (ae_restrict_iff_subtype (μ := (volume:Measure ℝ)) (s := Icc (0:ℝ) t)
      (p := fun s:ℝ => 0<Real.sin (Real.pi*s)*Real.sin (Real.pi*(t-s))/Real.pi^2) measurableSet_Icc).mp
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [jacobi.Reference.sineWeight,show (2:ℝ)-1=1 by norm_num,Real.rpow_one] using
      jacobi.Reference.sineWeight_pos 2 ht hs
  have hw (ε:ℝ) (hε:0<ε) : Integrable (fun s:Icc (0:ℝ) t => sineBase t s^(ε-1)) := by
    change Integrable (jacobi.Reference.sineWeight ε t ∘ Subtype.val)
      (Measure.comap (Subtype.val:Icc (0:ℝ) t→ℝ) volume)
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le).mp
        (jacobi.Reference.sineWeight_integrable hε ht))
  have h := jacobi.Analytic.positive_power_integral_holomorphic volume (sineBase t)
    (sineBase_product_nonneg ht) hpos hw H hg
  have heq (z:ℂ) : (∫ s:Icc (0:ℝ) t,(sineBase t s:ℂ)^(z-1)*H s)=
      ∫ s in (0:ℝ)..t,complexSineIntegrand z t omega s := by
    change (∫ s:Icc (0:ℝ) t,complexSineIntegrand z t omega s)=_
    rw [integral_subtype (s := Icc (0:ℝ) t) measurableSet_Icc
      (complexSineIntegrand z t omega),integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.1.le]
  refine ⟨?_,?_⟩
  · have hi : IntegrableOn (complexSineIntegrand g t omega) (Icc (0:ℝ) t) :=
      (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mpr h.1
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le).mpr hi
  · simpa only [heq] using h.2

end
end jacobi.ComplexReference
