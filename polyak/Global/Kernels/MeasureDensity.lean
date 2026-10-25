import polyak.Global.Kernels.Convolution

/-! The measure convolution is exactly the smooth density convolution. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function ContinuousLinearMap
open scoped Topology Convolution ContDiff ENNReal NNReal

theorem density_conv {f g : ℝ→ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf0 : ∀x,0≤f x) (hg0 : ∀x,0≤g x) :
    (volume.withDensity fun x=>ENNReal.ofReal (f x)).conv
      (volume.withDensity fun x=>ENNReal.ofReal (g x))=
    volume.withDensity (fun x=>ENNReal.ofReal ((f ⋆[mul ℝ ℝ] g) x)) := by
  rw [conv_withDensity_eq_lconvolution (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  rw [lconvolution_def]
  simp only [←sub_eq_neg_add,←ENNReal.ofReal_mul (hf0 _)]
  rw [←ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact hfc.convolutionExists_left (mul ℝ ℝ) hf
      (hg.integrable_of_hasCompactSupport (μ:=volume) hgc).locallyIntegrable x
  · exact ae_of_all _ fun t=>mul_nonneg (hf0 t) (hg0 (x-t))

@[simp] theorem phiMeasure_density : phiMeasure=volume.withDensity (fun x=>ENNReal.ofReal (phi x)) :=
  density_conv psi_smooth.continuous psi_smooth.continuous psi_compact psi_compact psi_nonneg psi_nonneg

@[simp] theorem kappaMeasure_density : kappaMeasure=volume.withDensity (fun x=>ENNReal.ofReal (kappa x)) := by
  rw [kappaMeasure,phiMeasure_density]
  exact density_conv phi_smooth.continuous phi_smooth.continuous phi_compact phi_compact phi_nonneg phi_nonneg

end polyak.Global.Kernels
