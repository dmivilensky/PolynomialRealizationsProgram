import jacobi.Analytic.YoungLower

/-!
Article: jacobi, Theorem 4.2.
The derivative of the actual explicit Young lower calibration is
computed throughout the original order range. Its value at U is
the exact rational number -13/75.
Use: youngLower_hasDerivAt proves the printed logarithmic derivative and exact contact slope of the original lower calibration.
-/
namespace jacobi.Parameter
noncomputable section
open Real

/-- The original second Bessel moment has the exact derivative determined by its actual rational formula.
Use: youngLower_hasDerivAt proves the printed logarithmic derivative and exact contact slope of the original lower calibration.
Article: jacobi, Theorem 4.2.
Proof: differentiate the actual polynomial denominator and its reciprocal; its original positive factors justify every cancellation. -/
theorem secondMoment_hasDerivAt {a:ℝ} (ha:-1<a) :
    HasDerivAt secondMoment (-secondMoment a*(2/(a+1)+1/(a+2))) a := by
  -- This is the actual Rayleigh moment already identified with the spectrum, rather than an independently specified parameter function.
  have h1 : a+1≠0 := by linarith
  have h2 : a+2≠0 := by linarith
  have hden := (((hasDerivAt_id a).add_const 1).pow 2).const_mul 4
  have hp := hden.mul ((hasDerivAt_id a).add_const 2)
  have h := hp.inv (mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ)≠0) (pow_ne_zero 2 h1)) h2)
  convert h using 1
  · ext x
    simp [secondMoment,one_div]
  · dsimp [secondMoment]
    field_simp [h1,h2]

/-- The genuine Young lower constant has exactly the source derivative throughout the full order range.
Use: youngLower_hasDerivAt_U supplies the original contact slope; Theorem 4.2's eventual upper comparison must have this same derivative at the common point.
Article: jacobi, Theorem 4.2.
Proof: differentiate the original positive fractional-power calibration using the proved actual second-moment derivative. The exact identity T^(3/4-1)=T^(3/4)/T cancels its same positive original moment. -/
theorem youngLower_hasDerivAt {a:ℝ} (ha:-1<a) :
    HasDerivAt youngLower (-(3/4:ℝ)*youngLower a*(2/(a+1)+1/(a+2))) a := by
  have hT := secondMoment_hasDerivAt ha
  have h := (hT.rpow_const (p:=(3/4:ℝ)) (Or.inl (secondMoment_pos ha).ne')).const_mul ((18/5:ℝ)^(1/4:ℝ))
  convert h using 1
  · rfl
  · rw [rpow_sub_one (secondMoment_pos ha).ne']
    unfold youngLower jacobi.Young.youngValue
    field_simp [(secondMoment_pos ha).ne']

/-- The actual original Young lower calibration has exactly the printed rational contact slope at U.
Use: Theorem 4.2's second-order comparison identifies the derivative of the actual upper constant and fibre infimum with this independently proved number.
Article: jacobi, Theorem 4.2.
Proof: specialize the full genuine derivative formula and the exact original value ell_Y(1/2)=2/15, then compute in the rational field. -/
theorem youngLower_hasDerivAt_U : HasDerivAt youngLower (-13/75) (1/2) := by
  have h := youngLower_hasDerivAt (a:=1/2) (by norm_num)
  norm_num only [youngLower_U] at h
  convert h using 1; norm_num

/-- The ordinary derivative of the actual original lower calibration at U is the printed rational number.
Use: the final Theorem 4.2 statement can cite the ordinary derivative in the article's exact notation.
Article: jacobi, Theorem 4.2.
Proof: the independently proved exact derivative witness determines the community ordinary derivative. -/
theorem youngLower_deriv_U : deriv youngLower (1/2)=-13/75 := youngLower_hasDerivAt_U.deriv

end
end jacobi.Parameter
