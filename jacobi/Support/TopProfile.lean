import jacobi.Support.TopValueBounds
import jacobi.Support.SineUniformLimit

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The genuine continuum normalization of the original support ground
solution. Its exact positive Gamma constant is kept separate from
the actual reference operator's endpoint normalization.
Use: topConstant and topValue_limit identify the actual top-node continuum amplitude, with the original beta dependence retained only in its normalization.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- The positive original support normalization constant before its pi power.
Use: topConstant and topValue_limit identify the actual top-node continuum amplitude, with the original beta dependence retained only in its normalization.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def topAmplitudeSquare (a b : ℝ) : ℝ :=
  Gamma (gamma b+1/2)/(averageGamma a b*Gamma (gamma a+1/2)*Gamma (2*averageGamma a b))

/-- The original support continuum amplitude has a genuinely strictly positive square throughout the entire source parameter range.
Use: topConstant_pos fixes the actual positive square-root branch of the exact printed normalization.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: every original Gamma argument and the original average exponent are positive in the source parameter range. -/
theorem topAmplitudeSquare_pos {a b : ℝ} (ha:-1<a) (hb:-1<b) : 0<topAmplitudeSquare a b := by
  have hg := parameter_pos ha hb
  exact div_pos (Gamma_pos_of_pos (by linarith [hg.2.1]))
    (mul_pos (mul_pos hg.2.2 (Gamma_pos_of_pos (by linarith [hg.1]))) (Gamma_pos_of_pos (by linarith [hg.2.2])))

/-- The original positive continuum normalization of the actual support ground solution.
Use: topProfile is the genuine printed U(t); topValue_limit fixes this exact amplitude for the actual finite original spectral polynomials.
Article: jacobi, Appendix C.3 (top-node polynomials).
-/
def topConstant (a b : ℝ) : ℝ := sqrt (topAmplitudeSquare a b)/π^(gamma a)

/-- The genuine original support continuum normalization is strictly positive.
Use: the top-node limit identifies the actual positive source profile U, with its exact original Gamma normalization.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: both the genuine Gamma-amplitude square root and the actual positive pi power are strictly positive. -/
theorem topConstant_pos {a b : ℝ} (ha:-1<a) (hb:-1<b) : 0<topConstant a b :=
  div_pos (sqrt_pos.mpr (topAmplitudeSquare_pos ha hb)) (rpow_pos_of_pos pi_pos _)

/-- The actual continuum top-node normalization has precisely the printed Gamma-square formula.
Use: topValue_limit compares the genuine finite squared amplitude with the original printed kappa_U^2.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: square its genuine positive definition, use the exact Gamma-amplitude square, and combine the two positive original pi powers. -/
theorem topConstant_sq {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    topConstant a b^2=Gamma (gamma b+1/2)/
      (averageGamma a b*π^(2*gamma a)*Gamma (gamma a+1/2)*Gamma (2*averageGamma a b)) := by
  -- The same literal printed Gamma quotient is obtained without introducing a free normalization parameter.
  rw [topConstant,div_pow,Real.sq_sqrt (topAmplitudeSquare_pos ha hb).le]
  have hpow : (π^gamma a)^2=π^(2*gamma a) := by
    rw [pow_two,← rpow_add pi_pos]
    congr 1
    ring
  rw [hpow,topAmplitudeSquare]
  ring

/-- The original support continuum top-node profile with its exact positive source normalization.
Use: topValue_uniform_half proves the full matrix half-chain top-node limit, including its middle index; the continuum normalized Volterra kernel cancels this same constant amplitude.
Article: jacobi, Appendix C.3 (top-node polynomials).
-/
def topProfile (a b t : ℝ) : ℝ := topConstant a b*(sin (π*t))^(gamma a)

/-- The genuine original support continuum top-node profile is continuous through its actual zero endpoint.
Use: compactness and the finite power bounds extend the positive-mesh top-node limit uniformly down to t=0.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the actual exponent gamma_alpha is strictly positive, so the original real power is continuous also at sine zeros. -/
theorem topProfile_continuous {a b : ℝ} (ha:-1<a) : Continuous (topProfile a b) := by
  have hg : 0≤gamma a := (parameter_pos ha ha).1.le
  exact continuous_const.mul ((continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const (fun _ => Or.inr hg))

/-- The original support top-node profile vanishes at its actual endpoint.
Use: topValue_uniform handles all original small mesh indices, including m=0, with the true continuous zero endpoint.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the sine vanishes and its genuine exponent gamma_alpha is positive. -/
theorem topProfile_zero {a b : ℝ} (ha:-1<a) : topProfile a b 0=0 := by
  simp [topProfile,Real.zero_rpow (parameter_pos ha ha).1.ne']

/-- The exact original top-node product exponents add to twice the genuine alpha exponent.
Use: topValue_limit normalizes its three genuine sine products without losing a degree power or a Gamma constant.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: positive-base real-power multiplication and division reduce the exact exponent sum to the literal definition of bar_gamma. -/
theorem top_power_product (a b : ℝ) {x : ℝ} (hx:0<x) :
    x*(x^(gamma a+1/2-1)/x^(gamma b+1/2-1))*x^(2*averageGamma a b-1)=x^(2*gamma a) := by
  -- Positive powers keep the same actual branch throughout the exact exponent cancellation.
  rw [← rpow_sub hx]
  calc
    _ = x^(1:ℝ)*x^((gamma a+1/2-1)-(gamma b+1/2-1))*x^(2*averageGamma a b-1) := by rw [rpow_one]
    _ = x^(1+((gamma a+1/2-1)-(gamma b+1/2-1))+(2*averageGamma a b-1)) := by rw [rpow_add hx,rpow_add hx]
    _ = _ := by congr 1; dsimp [averageGamma]; ring

end
end jacobi.Support
