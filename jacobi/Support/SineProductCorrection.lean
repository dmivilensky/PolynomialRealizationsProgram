import jacobi.Support.SineProducts
import jacobi.Reference.GammaRatio

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The original sine product is separated exactly into its rising-factor
Gamma ratio and the smooth log-sinc correction already developed for
chebyshev1. This shared correction handles arbitrary positive shifts
and nonintegral original frequencies.
Use: sineProduct_correction separates the genuine finite support amplitude into its exact Gamma factor and a uniformly controlled smooth correction.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial chebyshev1.SineJacobi

/-- The finite smooth logarithmic correction of the original sine product at any real positive lattice frequency.
Use: sineProduct_correction separates the genuine finite support amplitude into its exact Gamma factor and a uniformly controlled smooth correction.
Article: jacobi, Appendix C.3 (top-node polynomials).
-/
def sineCorrection (N s : ℝ) (m : ℕ) : ℝ :=
  ∑j∈Finset.range m,(logSinc (((j:ℝ)+s)/N)-logSinc (((j:ℝ)+1)/N))

/-- A genuine original sine quotient is its rising-factor quotient times the exact exponential log-sinc correction.
Use: sineProduct_correction proves the literal original finite product identity used by all support top-node asymptotics.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: both normalized arguments lie strictly between zero and one, so both sinc values are positive; exp(log u-log v)=u/v. Substituting sinc(x)=sin(x)/x gives the exact original quotient. -/
theorem sine_ratio_correction {N s : ℝ} (hN:0<N) (hs:0<s) (j : ℕ)
    (hjs:(j:ℝ)+s<N) (hj1:(j:ℝ)+1<N) :
    sin (((j:ℝ)+s)*(π/N))/sin (((j:ℝ)+1)*(π/N))=
      (((j:ℝ)+s)/((j:ℝ)+1))*exp (logSinc (((j:ℝ)+s)/N)-logSinc (((j:ℝ)+1)/N)) := by
  -- Positivity justifies the real logarithms and fixes the actual exponential factor without absolute values.
  have hj0 := Nat.cast_nonneg j (α:=ℝ)
  have hsa : ((j:ℝ)+s)/N∈Set.Ioo (-1:ℝ) 1 :=
    ⟨by have hp := div_pos (by linarith : 0<(j:ℝ)+s) hN; linarith,
      (div_lt_one hN).mpr hjs⟩
  have h1a : ((j:ℝ)+1)/N∈Set.Ioo (-1:ℝ) 1 :=
    ⟨by have hp := div_pos (by positivity : 0<(j:ℝ)+1) hN; linarith,
      (div_lt_one hN).mpr hj1⟩
  rw [logSinc,logSinc,exp_sub,exp_log (sinc_pi_pos hsa),exp_log (sinc_pi_pos h1a)]
  have hn : π*(((j:ℝ)+s)/N)≠0 := ne_of_gt (mul_pos pi_pos (div_pos (by linarith) hN))
  have hd : π*(((j:ℝ)+1)/N)≠0 := ne_of_gt (mul_pos pi_pos (div_pos (by positivity) hN))
  rw [sinc_of_ne_zero hn,sinc_of_ne_zero hd]
  have harg (t : ℝ) : t*(π/N)=π*(t/N) := by ring
  simp only [harg]
  field_simp

/-- The original finite sine product equals its exact rising-factor product times the exponential of its genuine smooth correction.
Use: the Gamma quotient limit and the uniform smooth correction estimate yield the original arbitrary-shift sine-product asymptotics used by the top-node limit and weights.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: apply the proved literal sine-factor identity at every original index, separate the finite products and combine the actual exponentials using exp(sum)=product(exp). -/
theorem sineProduct_correction {N s : ℝ} (hN:0<N) (hs:0<s) (m : ℕ)
    (hjs:∀j<m,(j:ℝ)+s<N) (hj1:∀j<m,(j:ℝ)+1<N) :
    sineProduct (π/N) s m=
      (∏j∈Finset.range m,((j:ℝ)+s)/((j:ℝ)+1))*exp (sineCorrection N s m) := by
  rw [sineProduct,sineCorrection,exp_sum,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  exact sine_ratio_correction hN hs j (hjs j (Finset.mem_range.mp hj)) (hj1 j (Finset.mem_range.mp hj))

end
end jacobi.Support
