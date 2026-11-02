import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: the elementary trigonometric and hyperbolic identities.
Use: sine_modulus_lower gives both lower bounds used to estimate the sine factor in the reflected original Delta_tau on its parity contours.
-/
namespace jacobi.Complex
noncomputable section
open Real _root_.Complex

/-- The actual complex sine modulus splits into a real sine square and an imaginary hyperbolic sine square.
Use: sine_modulus_lower gives both lower bounds used to estimate the sine factor in the reflected original Delta_tau on its parity contours.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: the classical identity abs(sin(x+i*y))^2=sin(x)^2+sinh(y)^2.
Proof: expand the real and imaginary parts, then use sin(x)^2+cos(x)^2=1 and cosh(y)^2-sinh(y)^2=1. -/
theorem sine_modulus_square (z : ℂ) :
    ‖Complex.sin z‖^2=(Real.sin z.re)^2+(Real.sinh z.im)^2 := by
  -- The identity retains both positive contributions instead of estimating a difference of exponentials.
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sin_eq]
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.add_im,
    Complex.sin_ofReal_re,Complex.sin_ofReal_im,Complex.cos_ofReal_re,Complex.cos_ofReal_im,
    Complex.cosh_ofReal_re,Complex.cosh_ofReal_im,Complex.sinh_ofReal_re,Complex.sinh_ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,zero_add,mul_one]
  linear_combination (Real.sin z.re)^2*(Real.cosh_sq_sub_sinh_sq z.im)+
    (Real.sinh z.im)^2*(Real.sin_sq_add_cos_sq z.re)

/-- Both the real sine and the imaginary hyperbolic sine are lower bounds for the actual complex sine modulus.
Use: contour_sine_lower handles respectively the bounded-imaginary and large-imaginary portions of the original half-integer frequency circles.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: discard one nonnegative square in sine_modulus_square and compare nonnegative square roots. -/
theorem sine_modulus_lower (z : ℂ) :
    |Real.sin z.re|≤‖Complex.sin z‖ ∧ |Real.sinh z.im|≤‖Complex.sin z‖ := by
  have h := sine_modulus_square z
  constructor <;> nlinarith [sq_nonneg (Real.sin z.re),sq_nonneg (Real.sinh z.im),
    sq_abs (Real.sin z.re),sq_abs (Real.sinh z.im),abs_nonneg (Real.sin z.re),
    abs_nonneg (Real.sinh z.im),norm_nonneg (Complex.sin z)]

/-- Away from zero, the real hyperbolic sine has a uniform positive exponential lower bound.
Use: contour_sine_lower controls the original reflected sine factor uniformly on the portion of each contour with imaginary frequency bounded away from zero.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: write sinh(u)=exp(u)*(1-exp(-2*u))/2 for u=abs(x), then use monotonicity of the exponential for u>=d>0. -/
theorem sinh_exponential_lower {d : ℝ} (hd : 0<d) {x : ℝ} (hx : d≤|x|) :
    0<(1-Real.exp (-2*d))/2 ∧
      ((1-Real.exp (-2*d))/2)*Real.exp |x|≤|Real.sinh x| := by
  -- The fixed gap d gives a strictly positive coefficient independent of x.
  have he := Real.exp_le_exp.mpr (show -2*|x|≤-2*d by linarith)
  have hval : Real.sinh |x|=Real.exp |x| * (1-Real.exp (-2*|x|))/2 := by
    rw [Real.sinh_eq,mul_sub,mul_one,← Real.exp_add,show |x|+(-2*|x|)= -|x| by ring]
  have habs : |Real.sinh x|=Real.sinh |x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h,abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
    · rw [abs_of_neg h,Real.sinh_neg,abs_of_neg (Real.sinh_neg_iff.mpr h)]
  refine ⟨by have h := Real.exp_lt_one_iff.mpr (show -2*d<0 by linarith); positivity,?_⟩
  rw [habs,hval]
  nlinarith [Real.exp_pos |x|]

end
end jacobi.Complex
