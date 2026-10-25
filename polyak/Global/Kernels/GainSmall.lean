import polyak.Global.Kernels.HatIntegral

/-! The literal quantitative low-frequency gain, including ξ=0. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function
open scoped Topology ENNReal NNReal

theorem phiHat_gap_integral (ξ:ℝ) : 1-phiHat ξ=∫x,(1-Real.cos (ξ*x))∂phiMeasure := by
  rw [integral_sub (integrable_const _) (cos_integrable _ ξ),phiHat_integral_cos]
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one]

theorem phiHat_gain_small {ξ:ℝ} (hξ:|ξ|≤2*Real.pi) :
    (2/Real.pi^2)*mPhi*ξ^2≤1-phiHat ξ := by
  rw [phiHat_gap_integral]
  have hi : Integrable (fun x:ℝ=>(2/Real.pi^2)*ξ^2*x^2) phiMeasure :=
    (phiMeasure_integrable_pow 2).const_mul _
  have hlow : (fun x:ℝ=>(2/Real.pi^2)*ξ^2*x^2)≤ᵐ[phiMeasure]
      (fun x=>1-Real.cos (ξ*x)) := by
    filter_upwards [phiMeasure_ae_support] with x hx
    have ht : |ξ*x|≤Real.pi := by
      rw [abs_mul]
      have hm := mul_le_mul hξ hx.le (abs_nonneg _) (by positivity:0≤2*Real.pi)
      nlinarith
    have hh := Real.cos_le_one_sub_mul_cos_sq ht
    nlinarith
  have hm := integral_mono_ae hi ((integrable_const _).sub (cos_integrable _ ξ)) hlow
  rw [integral_const_mul] at hm
  change (2/Real.pi^2)*ξ^2*mPhi≤∫x,1-Real.cos (ξ*x)∂phiMeasure at hm
  nlinarith [hm]

theorem kernelHat_gain_small {ε ξ:ℝ} (hξ:|ε*ξ|≤2*Real.pi) :
    (2/Real.pi^2)*mPhi*(ε*ξ)^2≤1-kernelHat ε ξ := by
  have hh := phiHat_gain_small hξ
  obtain ⟨hl,hu⟩ := phiHat_mem (ε*ξ)
  unfold kernelHat
  nlinarith

end polyak.Global.Kernels
