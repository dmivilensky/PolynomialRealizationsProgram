import jacobi.Reference.HarmonicSums

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The logarithmic inverse-square derivative majorant is genuinely
summable. The community real logarithm bound and p-series theorem
suffice, with no numerical tail certificate.
Use: the uniform regularized derivative theorem applies the community Weierstrass and differentiation theorems with this exact majorant.
-/
namespace jacobi.Reference
noncomputable section
open Real

/-- The actual logarithmic inverse-square bound used for the regularized spatial derivative is summable.
Use: the uniform regularized derivative theorem applies the community Weierstrass and differentiation theorems with this exact majorant.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: mathlib's log_le_rpow_div bounds log(k+2) by twice its square root. Since k+2<=2*(k+1), the terms are bounded by 2*sqrt(2)*(k+1)^(-3/2); apply the community p-series convergence theorem.
Source: the classical p-series test and logarithm-versus-power inequality, formalized in mathlib Analysis.PSeries and Analysis.SpecialFunctions.Pow.Real. -/
theorem logarithmic_inverse_square_summable :
    Summable (fun k : ℕ => Real.log (k+2:ℝ)/(k+1:ℝ)^2) := by
  -- This comparison holds at every original index, including the finite small-index prefix.
  have hp : Summable (fun k : ℕ => (k+1:ℝ)^(-(3/2:ℝ))) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1))
  apply (hp.mul_left (2*(2:ℝ)^(1/2:ℝ))).of_nonneg_of_le
  · intro k
    exact div_nonneg (Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) k])) (sq_nonneg _)
  · intro k
    have hk : 0<(k+1:ℝ) := by positivity
    have hlog := Real.log_le_rpow_div (by positivity : 0≤(k+2:ℝ)) (by norm_num : 0<(1/2:ℝ))
    have hpow : (k+2:ℝ)^(1/2:ℝ)≤(2*(k+1:ℝ))^(1/2:ℝ) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num)
    calc
      _ ≤ (2*(2*(k+1:ℝ))^(1/2:ℝ))/(k+1:ℝ)^2 := by gcongr; linarith
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hk.le]
        rw [show -(3/2:ℝ)=(1/2:ℝ)-2 by norm_num,Real.rpow_sub hk,Real.rpow_two]
        ring

end
end jacobi.Reference
