import jacobi.Analytic.HalfSineShiftedData
import jacobi.Analysis.HyperbolicSineSeries
import jacobi.GelfandLevitan.HalfSineClosed

/-!
Article: jacobi, Appendix E.1.
The exact original shifted sine series equals twice the Dirichlet Green
diagonal for every complex shift in the source slit domain. The removable
zero shift has its actual parabola value. The proof uses the verified
periodic cosh Fourier calculation and discharges all its premises from
the genuine original Bessel spectrum.
Use: half_sine_shifted_profile_square identifies the Fourier calculation with the same original spectral profile, rather than defining a substitute Green diagonal.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set jacobi.Reference jacobi.GelfandLevitan jacobi.Analysis

/-- The actual original shifted U profile has the literal complex sine-square series in the source normalization.
Use: half_sine_shifted_profile_square identifies the Fourier calculation with the same original spectral profile, rather than defining a substitute Green diagonal.
Article: jacobi, Appendix E.1.
Proof: substitute the genuine original U spectrum and normalized
spectral profiles in the actual shifted series and complexify the same real sine values. -/
theorem half_sine_shifted_series (ha:-1<(1/2:ℝ)) (t:Interval) (w:ℂ) :
    shiftedProfile (1/2) ha t w=
      ∑'k:ℕ,4*Complex.sin ((Real.pi:ℂ)*(k+1:ℂ)*(t:ℂ))^2/
        ((Real.pi:ℂ)^2*(k+1:ℂ)^2+w) := by
  rw [shiftedProfile]
  apply tsum_congr
  intro k
  rw [shiftedProfileTerm,shiftedEdge,half_sine_spectrum,half_sine_spectralProfile]
  push_cast
  ring

/-- The exact hyperbolic numerator difference is twice the source product.
Use: half_sine_shifted_profile_square gives the printed Green diagonal after the Fourier sum is evaluated.
Article: jacobi, Appendix E.1.
Proof: write r as rt+r(1-t), use the hyperbolic addition and subtraction
formulas, and cancel the common product of cosh factors. -/
theorem hyperbolic_diagonal_numerator (r t:ℂ) :
    Complex.cosh r-Complex.cosh (r*(1-2*t))=
      2*Complex.sinh (r*t)*Complex.sinh (r*(1-t)) := by
  calc
    _=Complex.cosh (r*t+r*(1-t))-Complex.cosh (r*(1-t)-r*t) := by
      congr 1 <;> congr 1 <;> ring
    _=_ := by rw [Complex.cosh_add,Complex.cosh_sub]; ring

/-- The original shifted U spectral profile is exactly the printed hyperbolic Green diagonal at every nonzero admissible square shift.
Use: half_sine_shifted_profile gives the closed principal-square-root formula on the entire original slit domain, including its removable zero value.
Article: jacobi, Appendix E.1.
Proof: the source domain excludes every genuine integer Fourier pole
and makes r*sinh(r) nonzero. Divide the actual convergent cosh Fourier
sine-square sum by that same factor and identify every term of the
original shifted spectral series. The remaining endpoint t=1 has both
the genuine sine series and hyperbolic numerator equal to zero. -/
theorem half_sine_shifted_profile_square (ha:-1<(1/2:ℝ)) (t:Interval)
    {r:ℂ} (hr:r≠0) (hw:r^2∈edgeDomain (1/2) ha) :
    shiftedProfile (1/2) ha t (r^2)=
      2*Complex.sinh (r*(t:ℂ))*Complex.sinh (r*(1-(t:ℂ)))/(r*Complex.sinh r) := by
  -- All Fourier premises come from the actual original U spectrum on the source slit plane.
  have hD := half_sine_all_denominators ha hr hw
  have hR := hyperbolic_denominator_ne hD
  have hsinh : Complex.sinh r≠0 := (mul_ne_zero_iff.mp hR).2
  by_cases ht:(t:ℝ)<1
  · have hs := (cosh_sine_hasSum r hD (half_sine_cosh_summable ha r hw) ⟨t.property.1,ht⟩).div_const
      (r*Complex.sinh r)
    rw [half_sine_shifted_series]
    calc
      _=∑'k:ℕ,(4*coshCoefficient r (k+1)*
          Complex.sin ((Real.pi:ℂ)*(k+1:ℂ)*(t:ℂ))^2)/(r*Complex.sinh r) := by
        apply tsum_congr
        intro k
        unfold coshCoefficient
        push_cast
        rw [add_comm (r^2) ((Real.pi:ℂ)^2*(k+1:ℂ)^2)]
        field_simp [hR,hsinh,hr]
      _=(Complex.cosh r-Complex.cosh (r*(1-2*(t:ℂ))))/(r*Complex.sinh r) := hs.tsum_eq
      _=_ := by rw [hyperbolic_diagonal_numerator]
  · have ht1 : (t:ℝ)=1 := le_antisymm t.property.2 (not_lt.mp ht)
    have hz : shiftedProfile (1/2) ha t (r^2)=0 := by
      rw [shiftedProfile]
      have hzero (k:ℕ) : shiftedProfileTerm (1/2) ha k t (r^2)=0 := by
        rw [shiftedProfileTerm,half_sine_spectralProfile]
        have hsin : Real.sin (Real.pi*(k+1:ℝ)*(t:ℝ))=0 := by
          rw [ht1,mul_one,mul_comm]
          simpa only [Nat.cast_add,Nat.cast_one] using Real.sin_nat_mul_pi (k+1)
        rw [hsin,zero_pow (by decide: (2:ℕ)≠0),mul_zero,Complex.ofReal_zero,mul_zero]
      simp only [hzero,tsum_zero]
    rw [hz,show (t:ℂ)=1 by exact_mod_cast ht1,sub_self,mul_zero,Complex.sinh_zero,mul_zero,zero_div]

/-- The genuine shifted U profile has the source's closed hyperbolic formula throughout its full complex slit domain, with the exact removable value at zero.
Use: this completes the printed special-case assertion following Theorem C.5 using the actual original profile and its previously proved holomorphy.
Article: jacobi, Appendix E.1.
Proof: for w!=0 use the actual principal square root, whose square is w,
in the completed exact square-shift theorem. At zero use the independently
proved original unshifted parabola, selecting its genuine removable value. -/
theorem half_sine_shifted_profile (ha:-1<(1/2:ℝ)) (t:Interval)
    {w:ℂ} (hw:w∈edgeDomain (1/2) ha) :
    shiftedProfile (1/2) ha t w=
      if w=0 then 2*(t:ℂ)*(1-(t:ℂ)) else
        2*Complex.sinh (Complex.sqrt w*(t:ℂ))*Complex.sinh (Complex.sqrt w*(1-(t:ℂ)))/
          (Complex.sqrt w*Complex.sinh (Complex.sqrt w)) := by
  -- The actual holomorphic profile provides the continuation at the removable origin.
  by_cases hw0:w=0
  · subst w
    rw [ite_eq_left rfl,shiftedProfile_zero,half_sine_persymmetricProfile]
    push_cast
    rfl
  · rw [ite_eq_right hw0]
    have hr : Complex.sqrt w≠0 := by
      intro h
      apply hw0
      rw [← frequency_square w,h,zero_pow (by decide: (2:ℕ)≠0)]
    simpa only [frequency_square] using half_sine_shifted_profile_square ha t hr
      (by simpa only [frequency_square] using hw)

end
end jacobi.EdgeResolvent
