import polyak.Global.Kernels.MeasureDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Compact support and the literal source second moments. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function ContinuousLinearMap
open scoped Topology Convolution ContDiff ENNReal NNReal

theorem phi_support_bound {x:ℝ} (hx:x∈support phi) : |x|<1/2 := by
  obtain ⟨u,hu,v,hv,he⟩ := support_convolution_subset (mul ℝ ℝ) hx
  rw [psi_support,Metric.mem_ball,Real.dist_eq,sub_zero] at hu hv
  rw [←he]
  exact (abs_add_le u v).trans_lt (by linarith)

theorem kappa_support_bound {x:ℝ} (hx:x∈support kappa) : |x|<1 := by
  obtain ⟨u,hu,v,hv,he⟩ := support_convolution_subset (mul ℝ ℝ) hx
  rw [←he]
  exact (abs_add_le u v).trans_lt (by linarith [phi_support_bound hu,phi_support_bound hv])

theorem phiMeasure_ae_support : ∀ᵐx∂phiMeasure,|x|<1/2 := by
  rw [phiMeasure_density,ae_withDensity_iff (μ:=volume) (f:=fun x=>ENNReal.ofReal (phi x))
    (ENNReal.measurable_ofReal.comp phi_smooth.continuous.measurable)]
  filter_upwards with x hx
  apply phi_support_bound
  change phi x≠0
  intro he
  simp [he] at hx

theorem kappaMeasure_ae_support : ∀ᵐx∂kappaMeasure,|x|<1 := by
  rw [kappaMeasure_density,ae_withDensity_iff (μ:=volume) (f:=fun x=>ENNReal.ofReal (kappa x))
    (ENNReal.measurable_ofReal.comp kappa_smooth.continuous.measurable)]
  filter_upwards with x hx
  apply kappa_support_bound
  change kappa x≠0
  intro he
  simp [he] at hx

@[simp] theorem integral_phiMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:ℝ→E) : ∫x,f x∂phiMeasure=∫x,phi x • f x := by
  rw [phiMeasure_density,integral_withDensity_eq_integral_toReal_smul (μ:=volume)
    (f:=fun x=>ENNReal.ofReal (phi x)) (ENNReal.measurable_ofReal.comp phi_smooth.continuous.measurable)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (phi_nonneg _)]

@[simp] theorem integral_kappaMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:ℝ→E) : ∫x,f x∂kappaMeasure=∫x,kappa x • f x := by
  rw [kappaMeasure_density,integral_withDensity_eq_integral_toReal_smul (μ:=volume)
    (f:=fun x=>ENNReal.ofReal (kappa x)) (ENNReal.measurable_ofReal.comp kappa_smooth.continuous.measurable)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (kappa_nonneg _)]

def mPhi : ℝ := ∫x,x^2∂phiMeasure

def mK : ℝ := ∫x,x^2∂kappaMeasure

theorem phiMeasure_integrable_pow (n:ℕ) : Integrable (fun x:ℝ=>x^n) phiMeasure := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [phiMeasure_ae_support] with x hx
  rw [Real.norm_eq_abs,abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith : |x|≤1) n).trans_eq (one_pow n)

theorem kappaMeasure_integrable_pow (n:ℕ) : Integrable (fun x:ℝ=>x^n) kappaMeasure := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [kappaMeasure_ae_support] with x hx
  rw [Real.norm_eq_abs,abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg x) hx.le n).trans_eq (one_pow n)

theorem mPhi_nonneg : 0≤mPhi := integral_nonneg fun _=>sq_nonneg _

theorem mK_nonneg : 0≤mK := integral_nonneg fun _=>sq_nonneg _

theorem phiMeasure_abs_first_le : ∫x:ℝ,|x|∂phiMeasure≤1/2 := by
  calc
    _ ≤ ∫_:ℝ,(1/2:ℝ)∂phiMeasure := integral_mono_ae
      ((phiMeasure_integrable_pow 1).congr (by simp)).norm
      (integrable_const _) (by filter_upwards [phiMeasure_ae_support] with x hx using hx.le)
    _ = 1/2 := by simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem psi_pos {x:ℝ} (hx:|x|<1/4) : 0<psi x := by
  apply lt_of_le_of_ne (psi_nonneg x)
  intro he
  have hn : x∈support psi := by
    rw [psi_support,Metric.mem_ball,Real.dist_eq,sub_zero]
    exact hx
  exact hn he.symm

theorem phi_one_eighth_pos : 0<phi (1/8) := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (f:=fun t:ℝ=>psi t*psi (1/8-t)) (x:=1/16)
  · exact psi_smooth.continuous.mul (psi_smooth.continuous.comp (continuous_const.sub continuous_id))
  · exact psi_compact.convolutionExists_left (mul ℝ ℝ) psi_smooth.continuous
      psi_integrable.locallyIntegrable (1/8)
  · intro t
    exact mul_nonneg (psi_nonneg t) (psi_nonneg _)
  · have h₁ : 0<psi (1/16) := psi_pos (by norm_num)
    have h₂ : (1/8:ℝ)-1/16=1/16 := by norm_num
    rw [h₂]
    exact (mul_pos h₁ h₁).ne'

theorem mPhi_pos : 0<mPhi := by
  rw [mPhi,integral_phiMeasure]
  apply integral_pos_of_integrable_nonneg_nonzero
    (f:=fun x:ℝ=>phi x*x^2) (x:=1/8)
  · exact phi_smooth.continuous.mul (continuous_id.pow 2)
  · exact (phi_smooth.continuous.mul (continuous_id.pow 2)).integrable_of_hasCompactSupport
      (phi_compact.mul_right)
  · intro x
    exact mul_nonneg (phi_nonneg x) (sq_nonneg x)
  · exact (mul_pos phi_one_eighth_pos (by norm_num)).ne'

end polyak.Global.Kernels
