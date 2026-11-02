import jacobi.Reference.WaveEquation

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
On the original half interval the true singular reference potential is
bounded by a fixed inverse square, the actual logarithmic slope by an
inverse first power, and the selected prefactor by the endpoint power.
These explicit bounds supply the coefficients of the high-frequency
energy estimate for the original reference equation.
Use: gives the exact spatial coefficient in u''=(Q_gamma-omega^2)*u in the frequency energy estimate.
-/
namespace jacobi.Reference
noncomputable section
open Real Set

/-- The actual reference potential after removing its fixed spectral shift.
Use: gives the exact spatial coefficient in u''=(Q_gamma-omega^2)*u in the frequency energy estimate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def singularPotential (a t : ℝ) : ℝ := potential a t- jacobi.Jacobi.endpointCorrection a

/-- The true physical sine has the uniform lower bound twice its original half-interval coordinate.
Use: bounds the actual singular potential and logarithmic derivative in the high-frequency energy argument.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: apply the community concavity bound sin(theta)>=2*theta/pi on the actual angular half interval. -/
theorem half_sine_lower {t : ℝ} (ht : t∈Ioc 0 (1/2)) : 2*t≤sin (Real.pi*t) := by
  have h := Real.mul_le_sin (x := Real.pi*t) (mul_nonneg Real.pi_pos.le ht.1.le) (by nlinarith [Real.pi_pos,ht.2])
  convert h using 1
  field_simp

/-- The true selected sine-power prefactor is bounded above by its original endpoint power on the whole half interval.
Use: controls the actual small-scale reference wave and its genuine slope at high frequency.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the actual sine base is positive and at most t; the genuine source exponent is positive, so real-power monotonicity applies. -/
theorem weight_half_bound {a : ℝ} (ha : -1<a) {t : ℝ} (ht : t∈Ioc 0 (1/2)) :
    weight a t≤t^(gamma a) := by
  have hs := sine_pos (show t∈Ioo 0 1 by constructor; exact ht.1; linarith [ht.2])
  apply Real.rpow_le_rpow (div_nonneg hs.le Real.pi_pos.le) ?_ (by linarith [(parameters ha).1])
  exact (div_le_iff₀ Real.pi_pos).mpr (by
    have hh := Real.sin_le (x := Real.pi*t) (mul_nonneg Real.pi_pos.le ht.1.le)
    nlinarith)

/-- The genuine singular reference potential has a global inverse-square bound on the source half interval.
Use: an explicit integrating factor propagates the high-frequency energy with a constant independent of frequency.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the true sine denominator is at least 2*t. Square that inequality,
keep the literal nonnegative numerator and divide by the positive
physical denominators. Increase the coefficient by one to make it positive. -/
theorem singularPotential_bound (a : ℝ) :
    ∃ A : ℝ,0<A ∧ ∀ t∈Ioc (0:ℝ) (1/2),|singularPotential a t|≤A/t^2 := by
  -- This holds for both signs of gamma*(gamma-1), including the attractive singular potential.
  let A := |gamma a*(gamma a-1)| *Real.pi^2/4+1
  refine ⟨A,by dsimp [A]; positivity,fun t ht => ?_⟩
  have htp : 0<t := ht.1
  have hs := half_sine_lower ht
  have hsp : 0<sin (Real.pi*t) := lt_of_lt_of_le (by linarith [ht.1] : (0:ℝ)<2*t) hs
  have hsq : 4*t^2≤sin (Real.pi*t)^2 := by nlinarith [sq_nonneg (sin (Real.pi*t)-2*t)]
  have hn : 0≤|gamma a*(gamma a-1)| *Real.pi^2 := by positivity
  have hh := div_le_div_of_nonneg_left hn (by positivity : (0:ℝ)<4*t^2) hsq
  dsimp [singularPotential,potential]
  rw [add_sub_cancel_right,abs_div,abs_mul,abs_of_nonneg (sq_nonneg Real.pi),abs_of_nonneg (sq_nonneg (sin (Real.pi*t)))]
  apply hh.trans
  dsimp [A]
  rw [show |gamma a*(gamma a-1)| * Real.pi^2/(4*t^2)=
    (|gamma a*(gamma a-1)| * Real.pi^2/4)/t^2 by ring]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)

/-- The actual logarithmic slope of the selected reference prefactor has a uniform inverse-distance bound.
Use: bounds the genuine initial spatial derivative in the high-frequency reference state.
Article: jacobi, Lemma C.1.
Proof: bound the actual cosine by one and the true sine below by twice the half-interval coordinate. -/
theorem weightLogSlope_bound (a : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ t∈Ioc (0:ℝ) (1/2),|weightLogSlope a t|≤B/t := by
  -- The uniform coefficient includes all allowed original orders, without requiring gamma>=1/2.
  refine ⟨|gamma a| *Real.pi/2+1,by positivity,fun t ht => ?_⟩
  have htp : 0<t := ht.1
  have hs := half_sine_lower ht
  have hsp : 0<sin (Real.pi*t) := lt_of_lt_of_le (by linarith [ht.1] : (0:ℝ)<2*t) hs
  have hn : |gamma a*Real.pi*cos (Real.pi*t)|≤|gamma a| *Real.pi := by
    rw [abs_mul,abs_mul,abs_of_pos Real.pi_pos]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  rw [weightLogSlope,abs_div,abs_of_pos hsp]
  have hh := div_le_div₀ (by positivity : 0≤|gamma a| *Real.pi) hn (by linarith [ht.1] : (0:ℝ)<2*t) hs
  apply hh.trans
  rw [show |gamma a| * Real.pi/(2*t)=(|gamma a| * Real.pi/2)/t by ring]
  exact div_le_div_of_nonneg_right (by linarith) ht.1.le

end
end jacobi.Reference
