import nesterov.Spread.Kernel
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Analysis.Asymptotics.Defs

/-! The positive source bump moment and the literal quartic Fourier germ. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
open polyak.Global.Kernels

theorem psiMeasure_ae_support : ∀ᵐ x ∂psiMeasure,|x|<1/4 := by
  rw [psiMeasure,ae_withDensity_iff (μ:=volume) (f:=fun x=>ENNReal.ofReal (psi x))
    (ENNReal.measurable_ofReal.comp psi_smooth.continuous.measurable)]
  filter_upwards with x hx
  have hh : x∈Function.support psi := by
    change psi x≠0
    intro he
    simp [he] at hx
  rw [psi_support,Metric.mem_ball,Real.dist_eq,sub_zero] at hh
  exact hh

theorem psiMeasure_integrable_pow (n : ℕ) : Integrable (fun x : ℝ=>x^n) psiMeasure := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [psiMeasure_ae_support] with x hx
  rw [Real.norm_eq_abs,abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith : |x|≤1) n).trans_eq (one_pow n)

def bumpMoment : ℝ := ∫x : ℝ,x^2∂psiMeasure

theorem bumpMoment_pos : 0<bumpMoment := by
  rw [bumpMoment,integral_psiMeasure]
  apply integral_pos_of_integrable_nonneg_nonzero
    (f:=fun x : ℝ=>psi x*x^2) (x:=1/8)
  · exact psi_smooth.continuous.mul (continuous_id.pow 2)
  · exact (psi_smooth.continuous.mul (continuous_id.pow 2)).integrable_of_hasCompactSupport psi_compact.mul_right
  · intro x
    exact mul_nonneg (psi_nonneg x) (sq_nonneg x)
  · exact (mul_pos (psi_pos (by norm_num)) (by norm_num)).ne'

theorem psiMeasure_first_moment : (∫x : ℝ,x∂psiMeasure)=0 := by
  rw [integral_psiMeasure]
  simp only [smul_eq_mul]
  have h := integral_neg_eq_self (fun x : ℝ=>psi x*x) (μ:=volume)
  simp only [psi_even,mul_neg,integral_neg] at h
  linarith

private theorem centered_square_add (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi1 : Integrable (fun y : ℝ=>y) μ) (hi2 : Integrable (fun y : ℝ=>y^2) μ)
    (hzero : (∫y : ℝ,y∂μ)=0) (x : ℝ) :
    (∫y : ℝ,(x+y)^2∂μ)=x^2+(∫y : ℝ,y^2∂μ) := by
    have heq : (fun y : ℝ=>(x+y)^2)=(fun y=>x^2+(2*x)*y+y^2) := by funext y;ring
    rw [heq]
    calc
      _ = (∫y : ℝ,x^2+2*x*y∂μ)+(∫y : ℝ,y^2∂μ) :=
        integral_add (f:=fun y : ℝ=>x^2+2*x*y) (g:=fun y : ℝ=>y^2)
          ((integrable_const (x^2)).add (hi1.const_mul (2*x))) hi2
      _ = _ := by
        rw [integral_add (f:=fun _ : ℝ=>x^2) (g:=fun y : ℝ=>2*x*y)
          (integrable_const (x^2)) (hi1.const_mul (2*x)),
          integral_const_mul,hzero]
        simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,mul_zero,add_zero]

theorem convolution_second_moment : mPhi=2*bumpMoment := by
  have h := integral_conv (show Integrable (fun x : ℝ=>x^2) (psiMeasure.conv psiMeasure)
    from phiMeasure_integrable_pow 2)
  change mPhi=(∫x : ℝ,∫y : ℝ,(x+y)^2∂psiMeasure∂psiMeasure) at h
  have hi1 : Integrable (fun y : ℝ=>y) psiMeasure := by simpa only [pow_one] using psiMeasure_integrable_pow 1
  have hinner (x : ℝ) : (∫y : ℝ,(x+y)^2∂psiMeasure)=x^2+bumpMoment :=
    centered_square_add psiMeasure hi1 (psiMeasure_integrable_pow 2) psiMeasure_first_moment x
  simp_rw [hinner] at h
  rw [integral_add (f:=fun x : ℝ=>x^2) (g:=fun _ : ℝ=>bumpMoment)
    (psiMeasure_integrable_pow 2) (integrable_const bumpMoment)] at h
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  change mPhi=bumpMoment+bumpMoment at h
  linarith

theorem phiHat_quartic_bound {ξ : ℝ} (hξ : |ξ|≤1) :
    |phiHat ξ-(1-mPhi*ξ^2/2)|≤((5/96:ℝ)*(∫x : ℝ,x^4∂phiMeasure))*|ξ|^4 := by
  have hp : Integrable (fun x : ℝ=>1-(ξ*x)^2/2) phiMeasure := by
    have heq : (fun x : ℝ=>1-(ξ*x)^2/2)=(fun x=>1-(ξ^2/2)*x^2) := by funext x;ring
    rw [heq]
    exact (integrable_const _).sub ((phiMeasure_integrable_pow 2).const_mul _)
  have hpoly : (∫x : ℝ,1-(ξ*x)^2/2∂phiMeasure)=1-mPhi*ξ^2/2 := by
    simp_rw [mul_pow,mul_div_assoc]
    rw [integral_sub (integrable_const _) ((phiMeasure_integrable_pow 2).const_mul (ξ^2/2) |>.congr
      (ae_of_all _ fun x=>by dsimp;ring))]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [show (fun x : ℝ=>ξ^2*(x^2/2))=(fun x=>(ξ^2/2)*x^2) by funext x;ring,integral_const_mul]
    dsimp [mPhi]
    ring
  have hI : Integrable (fun x : ℝ=>(|ξ|^4*(5/96:ℝ))*x^4) phiMeasure :=
    (phiMeasure_integrable_pow 4).const_mul _
  have hh := norm_integral_le_of_norm_le hI (show
      ∀ᵐ x ∂phiMeasure,‖Real.cos (ξ*x)-(1-(ξ*x)^2/2)‖≤(|ξ|^4*(5/96:ℝ))*x^4 from by
    filter_upwards [phiMeasure_ae_support] with x hx
    have harg : |ξ*x|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul hξ (by linarith : |x|≤1) (abs_nonneg x) (by norm_num)).trans_eq (by ring)
    have h := Real.cos_bound harg
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |ξ*x|^4*(5/96) := h
      _ = _ := by
        rw [abs_mul,mul_pow,show |x|^4=(|x|^2)^2 by ring,sq_abs]
        ring)
  rw [integral_sub (cos_integrable _ ξ) hp,←phiHat_integral_cos,hpoly,
    Real.norm_eq_abs,integral_const_mul] at hh
  nlinarith [hh]

theorem phiHat_quartic_germ :
    (fun ξ : ℝ=>phiHat ξ-(1-bumpMoment*ξ^2)) =O[𝓝 0] (fun ξ=>ξ^4) := by
  apply isBigO_iff.mpr
  refine ⟨(5/96:ℝ)*(∫x : ℝ,x^4∂phiMeasure),?_⟩
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with ξ hξ
  have hb : |ξ|≤1 := (show |ξ|<1 by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hξ).le
  have h := phiHat_quartic_bound hb
  rw [convolution_second_moment] at h
  simp only [Real.norm_eq_abs,abs_pow] at h ⊢
  simpa only [show 2*bumpMoment*ξ^2/2=bumpMoment*ξ^2 by ring] using h

end
end nesterov.Spread
