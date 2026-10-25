import polyak.Global.Kernels.HatIntegral

/-! The two quantitative variation bounds, uniform over every real frequency. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function
open scoped Topology ENNReal NNReal

theorem cos_difference_quadratic (a b:ℝ) :
    |Real.cos a-Real.cos b|≤|a+b| *|a-b| /2 := by
  rw [Real.cos_sub_cos,abs_mul,abs_mul]
  have h₁ := Real.abs_sin_le_abs (x:=(a+b)/2)
  have h₂ := Real.abs_sin_le_abs (x:=(a-b)/2)
  have hm := mul_le_mul h₁ h₂ (abs_nonneg _) (abs_nonneg _)
  rw [abs_div,abs_div] at hm
  norm_num at hm ⊢
  nlinarith

theorem phiHat_difference_linear (a b:ℝ) :
    |phiHat a-phiHat b|≤|a-b| /2 := by
  rw [phiHat_integral_cos,phiHat_integral_cos,←integral_sub (cos_integrable _ a) (cos_integrable _ b)]
  have hI : Integrable (fun x:ℝ=>|a-b| *|x|) phiMeasure := by
    simpa only [Real.norm_eq_abs] using ((phiMeasure_integrable_pow 1).congr (by simp)).norm.const_mul |a-b|
  have hn := norm_integral_le_of_norm_le hI (ae_of_all _ fun x=>show
    ‖Real.cos (a*x)-Real.cos (b*x)‖≤|a-b| *|x| from by
      rw [Real.norm_eq_abs,←abs_mul,sub_mul]
      exact Real.abs_cos_sub_cos_le _ _)
  rw [Real.norm_eq_abs,integral_const_mul] at hn
  exact hn.trans (by nlinarith [phiMeasure_abs_first_le,abs_nonneg (a-b)])

theorem phiHat_difference_quadratic (a b:ℝ) :
    |phiHat a-phiHat b|≤mPhi*|a+b| *|a-b| /2 := by
  rw [phiHat_integral_cos,phiHat_integral_cos,←integral_sub (cos_integrable _ a) (cos_integrable _ b)]
  have hI : Integrable (fun x:ℝ=>(|a+b| *|a-b| /2)*x^2) phiMeasure :=
    (phiMeasure_integrable_pow 2).const_mul _
  have hn := norm_integral_le_of_norm_le hI (ae_of_all _ fun x=>show
    ‖Real.cos (a*x)-Real.cos (b*x)‖≤(|a+b| *|a-b| /2)*x^2 from by
      have hh:=cos_difference_quadratic (a*x) (b*x)
      rw [←add_mul,←sub_mul,abs_mul,abs_mul] at hh
      rw [Real.norm_eq_abs]
      calc
        _ ≤ |a+b| *|x| *(|a-b| *|x|)/2 := hh
        _ = _ := by rw [←sq_abs x];ring)
  rw [Real.norm_eq_abs,integral_const_mul] at hn
  dsimp [mPhi]
  nlinarith [hn]

theorem square_difference_bound {a b:ℝ} (ha:a∈Icc (0:ℝ) 1) (hb:b∈Icc (0:ℝ) 1) :
    |a^2-b^2|≤2*|a-b| := by
  rcases ha with ⟨ha0,ha1⟩
  rcases hb with ⟨hb0,hb1⟩
  have he:a^2-b^2=(a-b)*(a+b) := by ring
  rw [he,abs_mul,abs_of_nonneg (by linarith:a+b≥0)]
  nlinarith [abs_nonneg (a-b)]

theorem kernelHat_difference_linear {ε:ℝ} (hε:0≤ε) (ξ η:ℝ) :
    |kernelHat ε ξ-kernelHat ε η|≤ε*|ξ-η| := by
  have h₁ := square_difference_bound (phiHat_mem (ε*ξ)) (phiHat_mem (ε*η))
  have h₂ := phiHat_difference_linear (ε*ξ) (ε*η)
  rw [←mul_sub,abs_mul,abs_of_nonneg hε] at h₂
  exact h₁.trans (by nlinarith)

theorem kernelHat_difference_quadratic {ε:ℝ} (hε:0≤ε) (ξ η:ℝ) :
    |kernelHat ε ξ-kernelHat ε η|≤mPhi*ε^2*|ξ+η| *|ξ-η| := by
  have h₁ := square_difference_bound (phiHat_mem (ε*ξ)) (phiHat_mem (ε*η))
  have h₂ := phiHat_difference_quadratic (ε*ξ) (ε*η)
  rw [←mul_add,←mul_sub,abs_mul,abs_mul,abs_of_nonneg hε] at h₂
  change |phiHat (ε*ξ)^2-phiHat (ε*η)^2|≤_
  nlinarith [h₁]

/-- Literal source D_n upper bound, for arbitrary real centers, hence for all signed integer n. -/
theorem kernelHat_local_variation {ε M ξ η:ℝ} (hε:0≤ε) (hM:0≤M) (hξη:|ξ-η|≤M) :
    |kernelHat ε ξ-kernelHat ε η|≤M*min (2*mPhi*ε^2*(|η|+M)) ε := by
  rw [mul_min_of_nonneg _ _ hM]
  apply le_min
  · have hh := kernelHat_difference_quadratic hε ξ η
    have ht : |ξ+η|≤2*(|η|+M) := by
      have he : ξ+η=(ξ-η)+2*η := by ring
      rw [he]
      exact (abs_add_le _ _).trans (by rw [abs_mul];norm_num;nlinarith)
    have hf := mul_le_mul ht hξη (abs_nonneg _) (by positivity:0≤2*(|η|+M))
    have hc : 0≤mPhi*ε^2 := mul_nonneg mPhi_nonneg (sq_nonneg _)
    have hp := mul_le_mul_of_nonneg_left hf hc
    nlinarith
  · have hh := kernelHat_difference_linear hε ξ η
    exact hh.trans (by nlinarith)

end polyak.Global.Kernels
