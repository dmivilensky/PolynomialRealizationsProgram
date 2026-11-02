import jacobi.Bessel.HalfInteger
import jacobi.Bessel.BetaConvolution
import jacobi.Reference.SecondSummationIntegral

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Poisson's integral is proved for the actual normalized Bessel function.
The original beta convolution, the genuine half-integer cosine identity
and the monotone quadratic substitution fix every normalization factor.
Source: Poisson's Bessel integral, DLMF 10.9.4.
Use: justifies the actual exponential splitting and endpoint Laplace estimate in the Bessel negative-axis asymptotic.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The original Poisson endpoint density is genuinely integrable throughout its full convergent order range.
Use: justifies the actual exponential splitting and endpoint Laplace estimate in the Bessel negative-axis asymptotic.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Poisson's integral, DLMF 10.9.4, and Euler's beta weight.
Proof: factor 1-s^2=(1-s)*(1+s). The first factor is the actual
integrable Jacobi endpoint weight, and the second is a continuous
positive-base power on the complete original interval. -/
theorem poisson_weight_integrable {a : ℝ} (ha : -(1/2:ℝ)<a) :
    IntervalIntegrable (fun s : ℝ => (1-s^2)^(a-1/2)) volume 0 1 := by
  -- Factoring the true endpoint distance isolates its only singular power.
  have hW := jacobi.Jacobi.weight_integrable (a := (0:ℝ)) (b := a-1/2) (by norm_num) (by linarith)
  have hC : ContinuousOn (fun s : ℝ => (1+s)^(a-1/2)) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    intro s hs
    exact ((continuousAt_const.add continuousAt_id).rpow_const
      (Or.inl (show 1+s≠0 by linarith [hs.1]))).continuousWithinAt
  apply (intervalIntegrable_congr_uIoo ?_).mp (hW.mul_continuousOn hC)
  intro s hs
  rw [uIoo_of_lt (by norm_num : (0:ℝ)<1)] at hs
  dsimp only [jacobi.Jacobi.weight]
  rw [Real.rpow_zero,one_mul,← Real.mul_rpow (sub_nonneg.mpr hs.2.le) (by linarith [hs.1])]
  congr 1
  ring

/-- Poisson's original integral has exactly the original normalized Bessel value at every complex frequency.
Use: the imaginary-frequency specialization and Watson endpoint limit compute the true Bessel characteristic's negative-axis normalization.
Article: jacobi, Appendix C.2 (norming ratios).
Source: Poisson's integral, DLMF 10.9.4, proved here from the original entire Bessel series.
Proof: apply the proved beta convolution at denominator parameter
one half. Substitute u=s^2 using the monotone theorem, so no bounded
endpoint assumption is imposed. The exact quadratic weight identity
and the genuine order -1/2 cosine identity identify the original
integrand and retain the Jacobian factor two. -/
theorem poisson_integral {a : ℝ} (ha : -(1/2:ℝ)<a) (w : ℂ) :
    2*(∫ s in (0:ℝ)..1,(((1-s^2)^(a-1/2):ℝ):ℂ)*Complex.cos (w*(s:ℂ)))=
      (Complex.Gamma (1/2:ℂ)*Complex.Gamma ((a:ℂ)+1/2)/Complex.Gamma ((a:ℂ)+1))*
        normalized (a:ℂ) (w^2) := by
  -- The actual beta convolution retains the original entire Bessel normalization before changing variables.
  let G : ℝ → ℂ := fun u => (jacobi.Jacobi.weight (-1/2) (a-1/2) u:ℂ)*
    normalized (-1/2) (w^2*(u:ℂ))
  have hb := beta_convolution (c := (1/2:ℝ)) (d := a+1/2) (by norm_num) (by linarith) (w^2)
  have hsum : (∫ u in (0:ℝ)..1,G u)=
      (Complex.Gamma (1/2:ℂ)*Complex.Gamma ((a:ℂ)+1/2)/Complex.Gamma ((a:ℂ)+1))*normalized (a:ℂ) (w^2) := by
    rw [show (1/2:ℝ)-1= -1/2 by ring,show a+1/2-1=a-1/2 by ring] at hb
    push_cast at hb
    rw [show (1/2:ℂ)-1= -1/2 by ring,
      show (1/2:ℂ)+((a:ℂ)+1/2)=(a:ℂ)+1 by ring,add_sub_cancel_right] at hb
    exact hb
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (0:ℝ)) (b := 1) (f := fun s : ℝ => s^2) (f' := fun s => 2*s) (g := G)
      (by fun_prop)
      (fun s _ => by convert! (hasDerivAt_id s).pow 2 using 1; simp)
      (fun s hs => by simp only [min_eq_left (by norm_num : (0:ℝ)≤1),max_eq_right (by norm_num : (0:ℝ)≤1),mem_Ioo] at hs; linarith [hs.1])
  norm_num only [zero_pow (by norm_num : 2≠0),one_pow,Function.comp_apply,Complex.real_smul] at hsub
  rw [← hsum,← hsub,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro s hs
  dsimp only [G]
  have hw := congrArg Complex.ofReal (jacobi.Reference.Hypergeometric.second_quadratic_pullback
    (1:ℝ) (a+1/2) hs)
  norm_num only [div_self (by norm_num : (1:ℝ)≠0),show (1:ℝ)/2-1= -1/2 by ring,
    show a+1/2-1=a-1/2 by ring,sub_self,Real.rpow_zero,mul_one] at hw
  push_cast at hw ⊢
  rw [show w^2*(s:ℂ)^2=(w*(s:ℂ))^2 by ring,normalized_neg_half]
  simp only [neg_div] at hw ⊢
  linear_combination -Complex.cos (w*(s:ℂ))*hw

end
end jacobi.Bessel
