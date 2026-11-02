import jacobi.Bessel.SturmIdentity

/-!
Article: jacobi, Theorem 2.1.
The actual Bessel equation generates a genuine Sturm--Liouville profile
on [0,1]. Its Green identity proves that every complex spectral zero is
positive real; no reality or positivity of a proposed zero list is assumed.
Source: the classical radial Sturm--Liouville argument with its regular
singular endpoint justified in SturmIdentity.
Use: interprets a zero at z as the Dirichlet endpoint of a genuine singular Sturm--Liouville solution.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized Bessel solution restricted to a radial spectral segment.
Use: interprets a zero at z as the Dirichlet endpoint of a genuine singular Sturm--Liouville solution.
Article: jacobi, Theorem 2.1.
-/
def radial (a : ℝ) (z : ℂ) (t : ℝ) : ℂ := normalized (a:ℂ) (z*t)

/-- The actual first radial derivative, including its spectral scaling.
Use: the Green primitive and the positive Rayleigh identity for true Bessel zeros.
Article: jacobi, Theorem 2.1.
-/
def radialSlope (a : ℝ) (z : ℂ) (t : ℝ) : ℂ := z*deriv (normalized (a:ℂ)) (z*t)

/-- The actual second radial derivative, with the full square of the spectral scaling.
Use: the literal radial Bessel differential equation.
Article: jacobi, Theorem 2.1.
-/
def radialAcceleration (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  z^2*deriv (deriv (normalized (a:ℂ))) (z*t)

/-- The actual radial Bessel profile and its first slope are continuous on the whole real line.
Use: discharges both endpoint continuity assumptions of the Green identity.
Article: jacobi, Theorem 2.1.
Proof: the normalized entire function and its genuine analytic
derivative are continuous; compose with the continuous spectral segment. -/
theorem radial_continuous (a : ℝ) (z : ℂ) :
    Continuous (radial a z) ∧ Continuous (radialSlope a z) := by
  -- Continuity is inherited from the actual analytic function, including the singular endpoint.
  have hF : Continuous (normalized (a:ℂ)) :=
    continuous_iff_continuousAt.mpr fun w => (normalized_analytic (a:ℂ) w).continuousAt
  have hD : Continuous (deriv (normalized (a:ℂ))) :=
    continuous_iff_continuousAt.mpr fun w => (normalized_analytic (a:ℂ) w).deriv.continuousAt
  exact ⟨hF.comp (continuous_const.mul Complex.continuous_ofReal),
    continuous_const.mul (hD.comp (continuous_const.mul Complex.continuous_ofReal))⟩

/-- The printed radial slope is the genuine ordinary real-parameter derivative of the actual profile.
Use: discharges the first differentiation premise of the singular Green identity.
Article: jacobi, Theorem 2.1.
Proof: compose the genuine complex derivative with multiplication by z,
restrict the parameter to the real axis and collect the scalar factors. -/
theorem radial_hasDerivAt (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (radial a z) (radialSlope a z t) t := by
  -- Restriction to real time retains the actual complex analytic derivative.
  have hF := (normalized_analytic (a:ℂ) (z*t)).differentiableAt.hasDerivAt
  have harg : HasDerivAt (fun w : ℂ => z*w) z (t:ℂ) := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (t:ℂ)).const_mul z
  convert (hF.comp (t:ℂ) harg).comp_ofReal using 1
  · rfl
  · unfold radialSlope
    ring

/-- The radial acceleration is the genuine ordinary derivative of the actual radial slope.
Use: discharges the second derivative premise of Green integration by parts.
Article: jacobi, Theorem 2.1.
Proof: apply the complex chain rule to the analytic first derivative,
restrict to real time and include the prefactor z. -/
theorem radialSlope_hasDerivAt (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (radialSlope a z) (radialAcceleration a z t) t := by
  -- The acceleration is derived from the existing function, rather than declared as an ODE certificate.
  have hF := (normalized_analytic (a:ℂ) (z*t)).deriv.differentiableAt.hasDerivAt
  have harg : HasDerivAt (fun w : ℂ => z*w) z (t:ℂ) := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (t:ℂ)).const_mul z
  convert ((hF.comp (t:ℂ) harg).comp_ofReal).const_mul z using 1
  · rfl
  · unfold radialAcceleration
    ring

/-- The genuine radial profile satisfies the exact singular Sturm--Liouville Bessel equation.
Use: the positive spectral identity applies to every actual Bessel zero.
Article: jacobi, Theorem 2.1.
Proof: multiply the actual entire spectral differential equation by
z/4 and collect the two chain-rule scaling factors. -/
theorem radial_equation {a : ℝ} (ha : -1<a) (z : ℂ) (t : ℝ) :
    (t:ℂ)*radialAcceleration a z t+(a+1:ℂ)*radialSlope a z t+(z/4)*radial a z t=0 := by
  unfold radial radialSlope radialAcceleration
  linear_combination (z/4)*(normalized_equation (a := (a:ℂ)) (by simpa using ha) (z*t))

/-- Every actual normalized Bessel zero has its genuine weighted Rayleigh identity.
Use: proves positive real location without assuming any spectral enumeration.
Article: jacobi, Theorem 2.1.
Proof: the actual entire function supplies both derivatives and all
endpoint continuity. At t=1 the assumed zero gives the Dirichlet boundary
value. Apply the proved weighted Green identity with every analytic premise discharged. -/
theorem zero_rayleigh_identity {a : ℝ} (ha : -1<a) {z : ℂ} (hz : normalized (a:ℂ) z=0) :
    (4:ℂ)*(∫ t in (0:ℝ)..1,‖radialSlope a z t‖^2*t^(a+1))=
      z*(∫ t in (0:ℝ)..1,‖radial a z t‖^2*t^a) := by
  -- The source zero is converted into an endpoint condition of this same actual profile.
  apply weighted_green_identity ha (radial a z) (radialSlope a z) (radialAcceleration a z)
    (radial_continuous a z).1 (radial_continuous a z).2
    (fun t _ => radial_hasDerivAt a z t) (fun t _ => radialSlope_hasDerivAt a z t)
    (fun t _ => radial_equation ha z t)
  simpa only [radial,Complex.ofReal_one,mul_one] using hz

/-- Every complex spectral zero of the actual normalized Bessel function is positive real when alpha>-1.
Use: identifies the genuine spectral zero set before positive-zero enumeration and canonical products.
Article: jacobi, Theorem 2.1.
Proof: normalization gives a nonzero radial solution at zero, hence a
strictly positive weighted norm. Green's identity writes z as four times
a nonnegative real energy divided by that positive norm. The normalized
central value excludes z=0, so the real quotient is strictly positive. -/
theorem normalized_zero_positive {a : ℝ} (ha : -1<a) {z : ℂ} (hz : normalized (a:ℂ) z=0) :
    ∃ ℓ : ℝ,0<ℓ ∧ z=(ℓ:ℂ) := by
  -- No reality premise is imposed on the candidate complex zero.
  have haC : -1<(a:ℂ).re := by simpa using ha
  have hz0 : z≠0 := by intro h; rw [h,normalized_zero haC] at hz; exact one_ne_zero hz
  let I := ∫ t in (0:ℝ)..1,‖radial a z t‖^2*t^a
  let J := ∫ t in (0:ℝ)..1,‖radialSlope a z t‖^2*t^(a+1)
  have hI : 0<I := weighted_norm_integral_pos ha (radial_continuous a z).1 (by
    simp only [radial,Complex.ofReal_zero,mul_zero,normalized_zero haC]
    exact one_ne_zero)
  have hJ : 0≤J := intervalIntegral.integral_nonneg (by norm_num : (0:ℝ)≤1) (fun t ht =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1 _))
  have he : z=((4*J/I:ℝ):ℂ) := by
    rw [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hI.ne')).mpr
    exact (zero_rayleigh_identity ha hz).symm
  have hp : 0≤4*J/I := div_nonneg (mul_nonneg (by norm_num) hJ) hI.le
  refine ⟨4*J/I,lt_of_le_of_ne hp ?_,he⟩
  intro h
  apply hz0
  rw [he,← h,Complex.ofReal_zero]

end
end jacobi.Bessel
