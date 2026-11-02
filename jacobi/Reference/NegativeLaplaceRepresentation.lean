import jacobi.Reference.NegativeKernel

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The original imaginary-frequency beta integral is written as a genuine
one-sided Laplace integral. Reflection of its actual symmetric sine
density fixes the exponential normalization exactly. The regular
endpoint coefficient has its true value B(gamma,gamma)^(-1).
Use: combines the two exponential terms of the genuine imaginary-frequency cosh integral in sineWeight_laplace_identity.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual sine beta density is exactly symmetric under reflection of its integration interval.
Use: combines the two exponential terms of the genuine imaginary-frequency cosh integral in sineWeight_laplace_identity.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: reflection exchanges the two original sine factors. -/
theorem sineWeight_reflection (g t s : ℝ) : sineWeight g t (t-s)=sineWeight g t s := by
  unfold sineWeight
  rw [sub_sub_cancel,mul_comm]

/-- The original symmetric sine-density cosh integral is exactly its one-sided Laplace integral times exp(t*y).
Use: proves wave_imaginary_laplace for the actual original reference function, with no asymptotic normalization assumption.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: write cosh as the half sum of its two actual exponentials.
Reflection s↦t-s makes their original weighted integrals equal.
Factoring exp(t*y) leaves the genuine Laplace weight exp(-2*y*s). -/
theorem sineWeight_laplace_identity {g t : ℝ} (hg : 0<g) (ht : t∈Ioo (0:ℝ) 1) (y : ℝ) :
    (∫ s in (0:ℝ)..t,sineWeight g t s*Real.cosh ((t-2*s)*y))=
      Real.exp (t*y)*(∫ s in (0:ℝ)..t,sineWeight g t s*Real.exp (-((2*y)*s))) := by
  -- Both actual exponential terms are genuinely integrable against the original singular sine density.
  let H : ℝ → ℝ := fun s => sineWeight g t s*Real.exp ((t-2*s)*y)
  let R : ℝ → ℝ := fun s => sineWeight g t s*Real.exp (-((t-2*s)*y))
  have hH : IntervalIntegrable H volume 0 t :=
    (sineWeight_integrable hg ht).mul_continuousOn (by fun_prop)
  have hR : IntervalIntegrable R volume 0 t :=
    (sineWeight_integrable hg ht).mul_continuousOn (by fun_prop)
  have hreflection : (fun s => H (t-s))=R := by
    funext s
    dsimp [H,R]
    rw [sineWeight_reflection]
    congr 2
    ring
  have hr : (∫ s in (0:ℝ)..t,R s)=∫ s in (0:ℝ)..t,H s := by
    rw [← hreflection,intervalIntegral.integral_comp_sub_left]
    simp only [sub_self,sub_zero]
  have hi : (∫ s in (0:ℝ)..t,sineWeight g t s*Real.cosh ((t-2*s)*y))=
      ∫ s in (0:ℝ)..t,H s := by
    calc
      _ = ∫ s in (0:ℝ)..t,(H s+R s)/2 := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [H,R]
        rw [Real.cosh_eq]
        ring
      _ = ((∫ s in (0:ℝ)..t,H s)+(∫ s in (0:ℝ)..t,R s))/2 := by
        rw [intervalIntegral.integral_div,intervalIntegral.integral_add hH hR]
      _ = _ := by rw [hr]; ring
  rw [hi,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp [H]
  rw [show (t-2*s)*y=t*y+(-((2*y)*s)) by ring,Real.exp_add]
  ring

/-- The actual imaginary-frequency reference wave has its exactly normalized one-sided Laplace representation.
Use: applies the endpoint Laplace limit to the same f used in the characteristic and GL constructions.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: use the proved literal beta representation, the exact reflected
cosh identity and exp(-t*y)*exp(t*y)=1. The original beta normalization
and sine prefactor are retained without changing the reference function. -/
theorem wave_imaginary_laplace {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) (y : ℝ) :
    Real.exp (-(t*y))*(wave a (Complex.I*(y:ℂ)) t).re=
      (betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)*
        (∫ s in (0:ℝ)..t,sineWeight (gamma a) t s*Real.exp (-((2*y)*s))) := by
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  rw [wave_beta_integral ha _ ⟨ht.1.le,ht.2⟩,betaWave_imaginary,Complex.ofReal_re,
    sineWeight_laplace_identity hg ht]
  rw [Real.exp_neg]
  field_simp

/-- The genuine regular coefficient of the normalized sine density is continuous at every physical regular point, including its selected endpoint.
Use: justifies the actual endpoint Laplace limit and the compact coefficient bound on a proper prefix of the original integration interval.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: both real-power bases are strictly positive; the sine and removable sinc factors are continuous there. -/
theorem betaDensityCoefficient_continuousAt {a t s : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hs : s∈Ico (0:ℝ) t) : ContinuousAt (fun r => betaDensityCoefficient a (t,r)) s := by
  have hbase : 0<Real.sinc (Real.pi*s)*(Real.sin (Real.pi*(t-s))/Real.pi) :=
    mul_pos (scaled_sinc_pos ⟨hs.1,hs.2.trans ht.2⟩)
      (div_pos (sine_pos ⟨sub_pos.mpr hs.2,by linarith [ht.2,hs.1]⟩) Real.pi_pos)
  have hb : ContinuousAt (fun r : ℝ =>
      Real.sinc (Real.pi*r)*(Real.sin (Real.pi*(t-r))/Real.pi)) s := by fun_prop
  exact continuousAt_const.mul (hb.rpow_const (Or.inl hbase.ne'))

/-- The original normalized sine density has its exact endpoint coefficient, independent of the physical point t.
Use: fixes the leading coefficient of the original reference negative-energy asymptotic before comparing characteristics.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: sinc(0)=1 and the two genuine positive-base sine powers have opposite exponents, so their product is exactly one. -/
theorem betaDensityCoefficient_zero (a : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    betaDensityCoefficient a (t,0)=(betaNormalization (gamma a))⁻¹ := by
  have hb : 0<Real.sin (Real.pi*t)/Real.pi := div_pos (sine_pos ht) Real.pi_pos
  simp only [betaDensityCoefficient,mul_zero,Real.sinc_zero,sub_zero,one_mul]
  rw [mul_assoc,← Real.rpow_add hb,show 1-gamma a+(gamma a-1)=(0:ℝ) by ring,
    Real.rpow_zero,mul_one]

end
end jacobi.Reference
