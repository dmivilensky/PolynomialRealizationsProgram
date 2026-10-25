import polyak.Global.Circle.SmoothConvolutionBasic

/-! The smooth density is exactly the measure convolution, by Fubini and Haar translation. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set Function
open scoped Topology ENNReal NNReal

theorem convolutionDensity_measure {K:Circle→ℝ} (hK:Continuous K) (hK0:∀x,0≤K x)
    (μ:Measure Circle) [IsFiniteMeasure μ] :
    (haar.withDensity (fun x=>ENNReal.ofReal (K x))).conv μ=
      haar.withDensity (fun x=>ENNReal.ofReal (convolutionDensity K μ x)) := by
  have hkmeas : Measurable (fun x=>ENNReal.ofReal (K x)) := ENNReal.measurable_ofReal.comp hK.measurable
  have hdmeas : Measurable (fun x=>ENNReal.ofReal (convolutionDensity K μ x)) :=
    ENNReal.measurable_ofReal.comp (continuous_convolutionDensity hK μ).measurable
  rw [Measure.conv_comm]
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [Measure.lintegral_conv hφ,lintegral_withDensity_eq_lintegral_mul _ hdmeas hφ]
  calc
    (∫⁻v,∫⁻t,φ (v+t)∂haar.withDensity (fun x=>ENNReal.ofReal (K x))∂μ)=
        ∫⁻v,∫⁻t,ENNReal.ofReal (K t)*φ (v+t)∂haar∂μ := by
      apply lintegral_congr
      intro v
      exact lintegral_withDensity_eq_lintegral_mul _ hkmeas
        (hφ.comp (measurable_const.add measurable_id))
    _ = ∫⁻v,∫⁻x,ENNReal.ofReal (K (x-v))*φ x∂haar∂μ := by
      apply lintegral_congr
      intro v
      have hh := lintegral_add_right_eq_self
        (fun x:Circle=>ENNReal.ofReal (K (x-v))*φ x) v (μ:=haar)
      simpa only [add_sub_cancel_right,add_comm v] using hh
    _ = ∫⁻x,∫⁻v,ENNReal.ofReal (K (x-v))*φ x∂μ∂haar :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻x,ENNReal.ofReal (convolutionDensity K μ x)*φ x∂haar := by
      apply lintegral_congr
      intro x
      rw [ofReal_convolutionDensity hK hK0 μ x]
      exact lintegral_mul_const'' (μ:=μ) (f:=fun v=>ENNReal.ofReal (K (x-v))) (φ x) (by fun_prop)

end polyak.Global.Circle
