import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
Article: jacobi, Theorem C.5.
An exact Fourier coefficient calculation for the continuous periodic cosh
arc supplies the original sine resolvent series. All frequencies and the
complex shift remain literal; no numerical approximation is used.
Source: the fundamental theorem of calculus and the additive-circle
Fourier theory in mathlib.
Use: cosh_fourier_integral evaluates every genuine integer Fourier coefficient of the periodic cosh arc.
-/
namespace jacobi.Analysis
noncomputable section
open Complex Set MeasureTheory

/-- An exact primitive for the original exponential times cosh Fourier integrand.
Use: cosh_fourier_integral evaluates every genuine integer Fourier coefficient of the periodic cosh arc.
Article: jacobi, Theorem C.5.
Proof: differentiate the genuine exponential and hyperbolic factors.
The mixed sinh terms cancel, leaving the nonzero scalar r^2-v^2. -/
theorem hyperbolic_exponential_primitive (r v:ℂ) (hD:r^2-v^2≠0) (x:ℝ) :
    HasDerivAt (fun s:ℝ => Complex.exp (-v*(s:ℂ))*
      (v*Complex.cosh (r*(1-(s:ℂ)))-r*Complex.sinh (r*(1-(s:ℂ))))/(r^2-v^2))
        (Complex.exp (-v*(x:ℂ))*Complex.cosh (r*(1-(x:ℂ)))) x := by
  -- Differentiate in the real integration variable with the original complex parameters fixed.
  have harg : HasDerivAt (fun s:ℝ => r*(1-(s:ℂ))) (-r) x := by
    simpa only [id_eq,Complex.ofReal_one,mul_neg,mul_one] using
      (((hasDerivAt_id x).ofReal_comp.const_sub 1).const_mul r)
  have hearg : HasDerivAt (fun s:ℝ => -v*(s:ℂ)) (-v) x := by
    simpa only [id_eq,Complex.ofReal_one,mul_one] using
      (hasDerivAt_id x).ofReal_comp.const_mul (-v)
  have he := (Complex.hasDerivAt_exp (-v*(x:ℂ))).comp x hearg
  have hc := (Complex.hasDerivAt_cosh (r*(1-(x:ℂ)))).comp x harg
  have hs := (Complex.hasDerivAt_sinh (r*(1-(x:ℂ)))).comp x harg
  convert (he.mul ((hc.const_mul v).sub (hs.const_mul r))).div_const (r^2-v^2) using 1
  · rfl
  · dsimp only [Function.comp_def,Pi.mul_apply,Pi.sub_apply]
    field_simp [hD]
    ring

/-- The original two-period complex cosh Fourier integral is evaluated exactly at every integer frequency.
Use: coshCircle_fourierCoeff identifies the actual additive-circle coefficients with their source resolvent denominators.
Article: jacobi, Theorem C.5.
Proof: integrate the proved genuine primitive on [0,2]. The integer
exponential has the same endpoint value one; cosh is even and sinh is odd,
so the endpoint difference is precisely twice r*sinh(r) divided by the original denominator. -/
theorem cosh_fourier_integral (r:ℂ) (n:ℤ)
    (hD:r^2+(Real.pi:ℂ)^2*(n:ℂ)^2≠0) :
    (∫x in (0:ℝ)..2,Complex.exp (-(Real.pi:ℂ)*(n:ℂ)*Complex.I*(x:ℂ))*
      Complex.cosh (r*(1-(x:ℂ))))=
        2*r*Complex.sinh r/(r^2+(Real.pi:ℂ)^2*(n:ℂ)^2) := by
  -- The genuine periodic endpoint identity is exact for arbitrary complex r.
  let v : ℂ := (Real.pi:ℂ)*(n:ℂ)*Complex.I
  have hv : r^2-v^2=r^2+(Real.pi:ℂ)^2*(n:ℂ)^2 := by
    dsimp only [v]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hd := fun x:ℝ => hyperbolic_exponential_primitive r v (by rwa [hv]) x
  have hc : Continuous (fun x:ℝ => Complex.exp (-v*(x:ℂ))*Complex.cosh (r*(1-(x:ℂ)))) := by fun_prop
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable (μ:=volume) 0 2)
  have he : Complex.exp (-v*2)=1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-n) using 1
    congr 1
    push_cast
    dsimp only [v]
    ring
  simp only [Complex.ofReal_ofNat,Complex.ofReal_zero,mul_zero,Complex.exp_zero,
    sub_zero,one_mul,show (1:ℂ)-2= -1 by norm_num,mul_neg_one,Complex.cosh_neg,
    Complex.sinh_neg,he,hv] at ht
  convert ht using 1
  · congr 1
    ext x
    congr 2
    dsimp only [v]
    ring
  · ring_nf

end
end jacobi.Analysis
