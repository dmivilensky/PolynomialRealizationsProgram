import chebyshev2.LocalObstruction.NormalizedCurve

/-!
Article: chebyshev2, Theorem 6.1.
The energy first variation along the actual normalization-preserving amplitude curves.
Use: `chebyshev2.LocalObstruction.tangent_energy_derivative` feeds
`chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient_with_property` (no local lower
bound of gradient with property).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory chebyshev2.SineContinuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Exact identity `(∫ x, (f x+a*w x)^3)=(∫ x, f x^3)+3*a*(∫ x, f x^2*w x)+ 3*a^2*(∫ x, f x*w
x^2)+a^3*(∫ x, w x^3)`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_cube_integral` rewrites with this identity
to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem cube_add_integral {f : ℝ → ℝ} (hf : Continuous f)
    (hi : Integrable (fun x => f x^3)) (w : SmoothTest) (a : ℝ) :
    (∫ x, (f x+a*w x)^3)=(∫ x, f x^3)+3*a*(∫ x, f x^2*w x)+
      3*a^2*(∫ x, f x*w x^2)+a^3*(∫ x, w x^3) := by
  -- Establish h₁ as the integrability justification for the later integral estimates or
  -- changes of order.
  have h₁ : Integrable (fun x => f x^2*w x) := by
    simpa only [Pi.pow_apply,mul_comm] using test_integrable w (hf.pow 2)
  -- Establish h₂ as the integrability justification for the later integral estimates or
  -- changes of order.
  have h₂ : Integrable (fun x => f x*w x^2) := by
    convert! test_integrable w (hf.mul w.property.1.continuous) using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  -- Establish h₃ as the integrability justification for the later integral estimates or
  -- changes of order.
  have h₃ : Integrable (fun x => w x^3) := by
    convert! test_integrable w (w.property.1.continuous.pow 2) using 1
    funext x
    simp only [Pi.pow_apply]
    ring
  have he : (fun x => (f x+a*w x)^3)=fun x =>
      f x^3+3*a*(f x^2*w x)+3*a^2*(f x*w x^2)+a^3*w x^3 := by
    funext x
    ring
  have he₁ := integral_add ((hi.add (h₁.const_mul (3*a))).add (h₂.const_mul (3*a^2))) (h₃.const_mul (a^3))
  have he₂ := integral_add (hi.add (h₁.const_mul (3*a))) (h₂.const_mul (3*a^2))
  have he₃ := integral_add hi (h₁.const_mul (3*a))
  simp only [Pi.add_apply] at he₁ he₂ he₃
  rw [he,he₁,he₂,he₃]
  simp only [integral_const_mul]

/--
Integrability of the displayed function: `Integrable (fun x => n x^3)`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_cube_integral` rewrites with this
integrability result to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sine_cube_integrable : Integrable (fun x => n x^3) := by
  convert! energy_integrable using 1
  funext x
  rw [sqrt_m,m]
  ring

/--
The precise assertion is `(∫ x, curveAmplitude h w t x^3)= (∫ x, n x^3)+3*t*(∫ x, n x^2*h
x)+3*t^2*(∫ x, n x*h x^2)+t^3*(∫ x, h x^3)+ 3*curveCorrection h w t*((∫ x, n x^2*w x)+2*t*(∫ x,
n x*h x*w x)+ t^2*(∫ x, h x^2*w x))+ 3*(curveCorrection h w t)^2*((∫ x, n x*w x^2)+t*(∫ x, h
x*w x^2))+ (curveCorrection h w t)^3*(∫ x, w x^3)`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_cube_derivative` uses this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun t => ∫ x, curveAmplitude
h w t x^3) (3*∫ x, n x^2*h x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem curveAmplitude_cube_integral (h w : SmoothTest) (t : ℝ) :
    (∫ x, curveAmplitude h w t x^3)=
    (∫ x, n x^3)+3*t*(∫ x, n x^2*h x)+3*t^2*(∫ x, n x*h x^2)+t^3*(∫ x, h x^3)+
    3*curveCorrection h w t*((∫ x, n x^2*w x)+2*t*(∫ x, n x*h x*w x)+
      t^2*(∫ x, h x^2*w x))+
    3*(curveCorrection h w t)^2*((∫ x, n x*w x^2)+t*(∫ x, h x*w x^2))+
    (curveCorrection h w t)^3*(∫ x, w x^3) := by
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : Continuous (fun x => n x+t*h x) :=
    n_continuous.add (continuous_const.mul h.property.1.continuous)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => (n x+t*h x)^3) := by
    have hd : HasCompactSupport (fun x => (n x+t*h x)^3-n x^3) := by
      apply h.property.2.mono
      intro x hx hz
      apply hx
      simp [hz]
    -- Establish continuity hc before using the function at limits or in calculus arguments.
    have hc : Continuous (fun x => (n x+t*h x)^3-n x^3) := (hcont.pow 3).sub (n_continuous.pow 3)
    convert! sine_cube_integrable.add (hc.integrable_of_hasCompactSupport hd) using 1
    funext x
    simp
  have hA : (∫ x, (n x+t*h x)^2*w x)=
      (∫ x, n x^2*w x)+2*t*(∫ x, n x*h x*w x)+t^2*(∫ x, h x^2*w x) := by
    have he : (fun x => (n x+t*h x)^2*w x)=fun x =>
        n x^2*w x+2*t*(n x*h x*w x)+t^2*(h x^2*w x) := by funext x; ring
    have h₁ := test_integrable w (g := fun x => n x^2) (n_continuous.pow 2)
    have h₂ := test_integrable w (g := fun x => n x*h x) (n_continuous.mul h.property.1.continuous)
    have h₃ := test_integrable w (g := fun x => h x^2) (h.property.1.continuous.pow 2)
    simp only [mul_comm (w _)] at h₁ h₂ h₃
    have he₁ := integral_add (h₁.add (h₂.const_mul (2*t))) (h₃.const_mul (t^2))
    have he₂ := integral_add h₁ (h₂.const_mul (2*t))
    simp only [Pi.add_apply] at he₁ he₂
    rw [he,he₁,he₂,integral_const_mul,integral_const_mul]
  have hB : (∫ x, (n x+t*h x)*w x^2)=(∫ x, n x*w x^2)+t*(∫ x, h x*w x^2) := by
    -- Establish h₁ as the integrability justification for the later integral estimates or
    -- changes of order.
    have h₁ : Integrable (fun x => n x*w x^2) := by
      convert! test_integrable w (n_continuous.mul w.property.1.continuous) using 1
      funext x; simp only [Pi.mul_apply]; ring
    -- Establish h₂ as the integrability justification for the later integral estimates or
    -- changes of order.
    have h₂ : Integrable (fun x => h x*w x^2) := by
      convert! test_integrable w (h.property.1.continuous.mul w.property.1.continuous) using 1
      funext x; simp only [Pi.mul_apply]; ring
    simp only [add_mul,mul_assoc]
    rw [integral_add h₁ (h₂.const_mul _),integral_const_mul]
  unfold curveAmplitude
  rw [cube_add_integral hcont hi w, cube_add_integral n_continuous sine_cube_integrable h,hA,hB]

/--
The actual derivative at the stated point: `HasDerivAt (fun t => ∫ x, curveAmplitude h w t x^3)
(3*∫ x, n x^2*h x) 0`.

Use: `chebyshev2.LocalObstruction.curveDensity_energy_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun t => ∫ x,
curveDensity h w t x*sqrt (curveDensity h w t x)) (3*∫ x, n x^2*h x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.curveCorrection_derivative`,
`chebyshev2.LocalObstruction.curveCorrection_zero`,
`chebyshev2.LocalObstruction.curveAmplitude_cube_integral` with the arguments shown in the
proof.
-/
theorem curveAmplitude_cube_derivative (h w : SmoothTest) (hw : 0<(∫ x, n x*w x)) :
    HasDerivAt (fun t => ∫ x, curveAmplitude h w t x^3) (3*∫ x, n x^2*h x) 0 := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.curveCorrection_derivative`,
  -- `chebyshev2.LocalObstruction.curveCorrection_zero`,
  -- `chebyshev2.LocalObstruction.curveAmplitude_cube_integral` with the arguments shown in
  -- the proof.
  have ht := hasDerivAt_id (0:ℝ)
  have ha := curveCorrection_derivative h w hw
  have hpoly := ((((((hasDerivAt_const (0:ℝ) (∫ x, n x^3)).add
    (ht.const_mul (3:ℝ) |>.mul_const (∫ x, n x^2*h x))).add
    ((ht.pow 2).const_mul (3:ℝ) |>.mul_const (∫ x, n x*h x^2))).add
    ((ht.pow 3).mul_const (∫ x, h x^3))).add
    ((ha.const_mul (3:ℝ)).mul
      (((hasDerivAt_const (0:ℝ) (∫ x, n x^2*w x)).add
        (ht.const_mul (2:ℝ) |>.mul_const (∫ x, n x*h x*w x))).add
        ((ht.pow 2).mul_const (∫ x, h x^2*w x))))).add
    (((ha.pow 2).const_mul (3:ℝ)).mul
      ((hasDerivAt_const (0:ℝ) (∫ x, n x*w x^2)).add
        (ht.mul_const (∫ x, h x*w x^2))))).add
    ((ha.pow 3).mul_const (∫ x, w x^3))
  simp only [Pi.pow_apply,id_eq,curveCorrection_zero] at hpoly
  norm_num at hpoly
  exact hpoly.congr_of_eventuallyEq (Eventually.of_forall (curveAmplitude_cube_integral h w))

/--
The actual derivative at the stated point: `HasDerivAt (fun t => ∫ x, curveDensity h w t x*sqrt
(curveDensity h w t x)) (3*∫ x, n x^2*h x) 0`.

Use: `chebyshev2.LocalObstruction.tangent_energy_derivative` uses this derivative formula
to establish the actual derivative at the stated point: `HasDerivAt (fun t => ∫ x, curveDensity
(amplitudeDirection v) w t x* sqrt (curveDensity (amplitudeDirection v) w t x)) (∫ x, v
x*((3/2:ℝ)*n x)) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem curveDensity_energy_derivative (h w : SmoothTest) (hw : 0<(∫ x, n x*w x)) :
    HasDerivAt (fun t => ∫ x, curveDensity h w t x*sqrt (curveDensity h w t x))
      (3*∫ x, n x^2*h x) 0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (curveAmplitude_cube_derivative h w hw).congr_of_eventuallyEq
  filter_upwards [curveAmplitude_positive h w hw] with t ht
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change curveDensity h w t x*sqrt (curveDensity h w t x)=curveAmplitude h w t x^3
    rw [curveDensity,sqrt_sq (ht x).le]
    ring)

/--
The actual derivative at the stated point: `HasDerivAt (fun t => ∫ x, curveDensity
(amplitudeDirection v) w t x* sqrt (curveDensity (amplitudeDirection v) w t x)) (∫ x, v
x*((3/2:ℝ)*n x)) 0`.

Use: `chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient` uses this derivative
formula to construct witnesses satisfying `∃ f : ℝ → ℝ, ContDiff ℝ ∞
(fun x => f x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x,
sqrt (f x))=1 ∧ (∀ x, |f x-m x|<ε) ∧ densityEnergy f<B f`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem tangent_energy_derivative (v w : SmoothTest) (hw : 0<(∫ x, n x*w x)) :
    HasDerivAt (fun t => ∫ x, curveDensity (amplitudeDirection v) w t x*
      sqrt (curveDensity (amplitudeDirection v) w t x))
      (∫ x, v x*((3/2:ℝ)*n x)) 0 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he : (fun x => n x^2*amplitudeDirection v x)=fun x => (v x*((3/2:ℝ)*n x))/3 := by
    funext x
    change n x^2*(v x/(2*n x))=v x*(3/2*n x)/3
    field_simp [(n_positive x).ne']
  convert! curveDensity_energy_derivative (amplitudeDirection v) w hw using 1
  rw [he,integral_div]
  ring

end
end chebyshev2.LocalObstruction
