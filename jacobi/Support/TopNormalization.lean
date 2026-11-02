import jacobi.Support.TopProfile

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
Exact real-power and Gamma normalizations for the actual top-node limit.
These identities retain the genuine source constant and both original
endpoint exponents when the three finite sine products are combined.
Use: top_finite_normalization combines the actual convergent factors without assuming a big-O power cancellation.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- The three genuine finite product normalizations and original linear factor have exactly the degree power required by the squared top-node limit.
Use: top_finite_normalization combines the actual convergent factors without assuming a big-O power cancellation.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: combine positive-base real powers and expand the literal original average exponent. -/
theorem top_degree_power (a b : ℝ) {x : ℝ} (hx:0<x) :
    ((x^(1-(gamma a+1/2)))/(x^(1-(gamma b+1/2))))*x^(1-2*averageGamma a b)/x=x^(-2*gamma a) := by
  rw [← rpow_sub hx,← rpow_add hx,← rpow_sub_one hx.ne']
  congr 1
  dsimp [averageGamma]
  ring

/-- The genuine normalized finite top-node product is exactly its original squared-value normalization.
Use: topValue_square_limit inserts the actual finite sine factors into the same limit calculation, before any limiting replacement is made.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: collect the actual positive degree powers separately from the original scalar product and apply their proved exact exponent identity. -/
theorem top_finite_normalization (a b : ℝ) {x : ℝ} (hx:0<x) (S A B D : ℝ) :
    (S/x)*((x^(1-(gamma a+1/2))*A)/(x^(1-(gamma b+1/2))*B))*(x^(1-2*averageGamma a b)*D)=
      x^(-2*gamma a)*(S*(A/B)*D) := by
  calc
    _ = (((x^(1-(gamma a+1/2)))/(x^(1-(gamma b+1/2))))*x^(1-2*averageGamma a b)/x)*(S*(A/B)*D) := by ring
    _ = _ := by rw [top_degree_power a b hx]

/-- The original limiting sine-product constants combine to the exact printed positive Gamma amplitude.
Use: topValue_square_limit identifies the actual source constant rather than merely proving convergence to an unspecified multiple of the ground profile.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: collect the exact three original Gamma factors and apply the original top-product exponent identity to the positive sine coordinate. -/
theorem top_limit_constant (a b : ℝ) {x : ℝ} (hx:0<x) :
    (x/averageGamma a b)*
      (((Gamma (gamma a+1/2))⁻¹*x^(gamma a+1/2-1))/
        ((Gamma (gamma b+1/2))⁻¹*x^(gamma b+1/2-1)))*
      ((Gamma (2*averageGamma a b))⁻¹*x^(2*averageGamma a b-1))=
        topAmplitudeSquare a b*x^(2*gamma a) := by
  calc
    _ = topAmplitudeSquare a b*(x*(x^(gamma a+1/2-1)/x^(gamma b+1/2-1))*x^(2*averageGamma a b-1)) := by
      dsimp [topAmplitudeSquare]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    _ = _ := by rw [top_power_product a b hx]

/-- The genuine printed top-node continuum profile has the exact original normalized sine-power square.
Use: topValue_square_limit takes its actual nonnegative square root to identify the genuine U profile.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: square the actual positive Gamma normalization and combine positive pi powers. The actual sine power has its genuine nonnegative branch, including a possible zero endpoint. -/
theorem topProfile_sq {a b t : ℝ} (ha:-1<a) (hb:-1<b) (ht:0≤sin (π*t)) :
    (topProfile a b t)^2=topAmplitudeSquare a b*(sin (π*t)/π)^(2*gamma a) := by
  -- The exponent is genuinely positive, so the original endpoint case is retained by the real-power identity.
  have hg := (parameter_pos ha hb).1.le
  have hsquare (x : ℝ) (hx:0≤x) : (x^gamma a)^2=x^(2*gamma a) := by
    rw [pow_two,← rpow_add_of_nonneg hx hg hg]
    congr 1
    ring
  rw [topProfile,mul_pow,topConstant,div_pow,Real.sq_sqrt (topAmplitudeSquare_pos ha hb).le,
    hsquare π pi_pos.le,hsquare (sin (π*t)) ht,Real.div_rpow ht pi_pos.le]
  ring

end
end jacobi.Support
