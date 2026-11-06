import nesterov.Spread.KernelBand
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The affine probability is exactly the source density w⁻¹ k((freq-freq₀)/w). -/
namespace nesterov.Spread
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
open polyak.Global.Kernels

def affineEquiv (center width : ℝ) (hw : width≠0) : ℝ ≃ᵐ ℝ where
  toFun x := center+width*x
  invFun x := (x-center)/width
  left_inv x := by field_simp;ring
  right_inv x := by field_simp;ring
  measurable_toFun := by change Measurable (fun x : ℝ=>center+width*x);fun_prop
  measurable_invFun := by change Measurable (fun x : ℝ=>(x-center)/width);fun_prop

def bandDensity (center width freq : ℝ) : ℝ := width⁻¹*phi ((freq-center)/width)

theorem bandDensity_smooth (center width : ℝ) : ContDiff ℝ ∞ (bandDensity center width) := by
  have h : ContDiff ℝ ∞ (fun freq : ℝ=>(freq-center)/width) := by fun_prop
  exact contDiff_const.mul (phi_smooth.comp h)

theorem bandDensity_nonneg (center : ℝ) {width : ℝ} (hw : 0<width) (freq : ℝ) :
    0≤bandDensity center width freq := mul_nonneg (inv_nonneg.mpr hw.le) (phi_nonneg _)

theorem bandDensity_integrable (center : ℝ) {width : ℝ} (hw : 0<width) :
    Integrable (bandDensity center width) := by
  let e : ℝ ≃ₜ ℝ := {
    toEquiv := (affineEquiv center width hw.ne').toEquiv
    continuous_toFun := by change Continuous (fun x : ℝ=>center+width*x);fun_prop
    continuous_invFun := by change Continuous (fun x : ℝ=>(x-center)/width);fun_prop }
  have hc : Continuous (bandDensity center width) :=
    continuous_const.mul (phi_smooth.continuous.comp ((continuous_id.sub continuous_const).div_const width))
  apply hc.integrable_of_hasCompactSupport
  have hk := phi_compact.comp_homeomorph e.symm
  change HasCompactSupport (fun x : ℝ=>width⁻¹*phi (e.symm x))
  exact hk.mul_left

theorem bandMeasure_density (center : ℝ) {width : ℝ} (hw : 0<width) :
    bandMeasure center width=
      volume.withDensity (fun freq=>ENNReal.ofReal (bandDensity center width freq)) := by
  let e := affineEquiv center width hw.ne'
  have hd (x : ℝ) : HasDerivAt (e.symm : ℝ→ℝ) (width⁻¹) x := by
    change HasDerivAt (fun z : ℝ=>(z-center)/width) (width⁻¹) x
    convert ((hasDerivAt_id x).sub_const center).div_const width using 1 <;>
      simp only [id_eq,one_div]
  apply Measure.ext
  intro s hs
  have hj := e.symm.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    hs hd (ae_of_all _ phi_nonneg) phi_integrable
  change (volume.withDensity (fun x=>ENNReal.ofReal (phi x))).map
    (fun x=>center+width*x) s=_ at hj
  rw [bandMeasure,phiMeasure_density]
  rw [hj,withDensity_apply _ hs,
    ←ofReal_integral_eq_lintegral_ofReal (bandDensity_integrable center hw).integrableOn
      (ae_of_all _ (bandDensity_nonneg center hw))]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  change |width⁻¹| * phi ((x-center)/width)=width⁻¹*phi ((x-center)/width)
  rw [abs_of_pos (inv_pos.mpr hw)]

end
end nesterov.Spread
