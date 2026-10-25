import chebyshev2.LocalObstruction.AmplitudeDirections
import chebyshev2.LocalObstruction.QuadraticCorrection

/-!
Article: chebyshev2, Theorem 6.1.
Explicit normalization-preserving curves through the sine density.
Use: `chebyshev2.LocalObstruction.curveDensity_increment` feeds
`chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient_with_property` (no local lower
bound of gradient with property).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory chebyshev2.SineContinuum
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000

 /--
Exact identity `(∫ x, (f x+a*w x)^2)=(∫ x, f x^2)+2*a*(∫ x, f x*w x)+a^2*(∫ x, w x^2)`.

Use: `chebyshev2.LocalObstruction.curveDensity_mass` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), (∫
x, curveDensity h w t x)=1`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem square_add_integral {f : ℝ → ℝ} (hf : Continuous f)
    (hi : Integrable (fun x => f x^2)) (w : SmoothTest) (a : ℝ) :
    (∫ x, (f x+a*w x)^2)=(∫ x, f x^2)+2*a*(∫ x, f x*w x)+a^2*(∫ x, w x^2) := by
  -- Establish hcross as the integrability justification for the later integral estimates or
  -- changes of order.
  have hcross : Integrable (fun x => f x*w x) := by
    simpa only [mul_comm] using test_integrable w hf
  -- Establish hsq as the integrability justification for the later integral estimates or
  -- changes of order.
  have hsq : Integrable (fun x => w x^2) := by
    simpa only [pow_two] using test_integrable w w.property.1.continuous
  have he : (fun x => (f x+a*w x)^2)=fun x => f x^2+2*a*(f x*w x)+a^2*w x^2 := by
    funext x
    ring
  have he₁ := integral_add (hi.add (hcross.const_mul (2*a))) (hsq.const_mul (a^2))
  have he₂ := integral_add hi (hcross.const_mul (2*a))
  simp only [Pi.add_apply] at he₁ he₂
  rw [he,he₁,he₂,integral_const_mul,integral_const_mul]

 /--
Defines `curveCorrection` of type `ℝ` by `quadraticCorrection (2*∫ x, n x*w x) (∫ x, h x*w x)
(∫ x, w x^2) (∫ x, h x^2) t`.

Use: `chebyshev2.LocalObstruction.curveAmplitude` uses this definition in the displayed
construction of `curveAmplitude`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def curveCorrection (h w : SmoothTest) (t : ℝ) : ℝ :=
  quadraticCorrection (2*∫ x, n x*w x) (∫ x, h x*w x)
    (∫ x, w x^2) (∫ x, h x^2) t

 /--
Defines `curveAmplitude` of type `ℝ` by `n x+t*h x+curveCorrection h w t*w x`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_mass` uses this definition to establish
exact identity `(∫ x, curveAmplitude h w t x)=1`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def curveAmplitude (h w : SmoothTest) (t x : ℝ) : ℝ :=
  n x+t*h x+curveCorrection h w t*w x

 /--
Defines `curveDensity` of type `ℝ` by `(curveAmplitude h w t x)^2`.

Use: `chebyshev2.LocalObstruction.curveDensity_increment` uses this definition to establish
smoothness to the stated order: `ContDiff ℝ ∞ (fun x => curveDensity h w t x-m x) ∧
HasCompactSupport (fun x => curveDensity h w t x-m x)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def curveDensity (h w : SmoothTest) (t x : ℝ) : ℝ := (curveAmplitude h w t x)^2

 /--
Exact identity `curveCorrection h w 0=0`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_positive` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
0<curveAmplitude h w t x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.quadraticCorrection_zero`
with the arguments shown in the proof.
-/
theorem curveCorrection_zero (h w : SmoothTest) : curveCorrection h w 0=0 :=
  quadraticCorrection_zero

 /--
The actual derivative at the stated point: `HasDerivAt (curveCorrection h w) 0 0`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_positive` uses this derivative formula to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
0<curveAmplitude h w t x`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.quadraticCorrection_derivative` with the arguments shown in
the proof.
-/
theorem curveCorrection_derivative (h w : SmoothTest) (hw : 0<(∫ x, n x*w x)) :
    HasDerivAt (curveCorrection h w) 0 0 :=
  quadraticCorrection_derivative (mul_pos (by norm_num) hw)

 /--
Exact identity `curveAmplitude h w 0 x=n x`.

Use: `chebyshev2.LocalObstruction.curveDensity_zero` rewrites with this identity to
establish exact identity `curveDensity h w 0=m`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.curveCorrection_zero` with
the arguments shown in the proof.
-/
theorem curveAmplitude_zero (h w : SmoothTest) (x : ℝ) : curveAmplitude h w 0 x=n x := by simp [curveAmplitude,curveCorrection_zero]

 /--
Exact identity `curveDensity h w 0=m`.

Use: `chebyshev2.LocalObstruction.curveDensity_uniform_small` uses this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
|curveDensity h w t x-m x|<ε`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem curveDensity_zero (h w : SmoothTest) : curveDensity h w 0=m := by
  funext x
  simp only [curveDensity,curveAmplitude_zero,m]

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
0<curveAmplitude h w t x`.

Use: `chebyshev2.LocalObstruction.curveDensity_energy_derivative` uses this bound to
establish the actual derivative at the stated point: `HasDerivAt (fun t => ∫ x, curveDensity h
w t x*sqrt (curveDensity h w t x)) (3*∫ x, n x^2*h x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Check each member of the finite index type; no case
is omitted.
-/
theorem curveAmplitude_positive (h w : SmoothTest) (hw : 0<(∫ x, n x*w x)) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ x, 0<curveAmplitude h w t x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let v : Fin 2 → ℝ → ℝ := ![h,w]
  let a : ℝ → Fin 2 → ℝ := fun t => ![t,curveCorrection h w t]
  have hv : ∀ i, Continuous (v i) := by
    intro i
    fin_cases i
    · simpa [v] using h.property.1.continuous
    · simpa [v] using w.property.1.continuous
  have hc : ∀ i, HasCompactSupport (v i) := by
    intro i
    fin_cases i
    · simpa [v] using h.property.2
    · simpa [v] using w.property.2
  -- Record the convergence ha with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ha : Tendsto a (𝓝 (0:ℝ)) (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_id
    · simpa [a,curveCorrection_zero] using (curveCorrection_derivative h w hw).continuousAt.tendsto
  have he := ha.eventually (finite_perturbation_positive n_continuous n_positive (v := v) hv hc)
  filter_upwards [he] with t ht x
  simpa [perturb,v,a,Fin.sum_univ_two,curveAmplitude,add_assoc] using ht x

 /--
Integrability of the displayed function: `Integrable (curveAmplitude h w t)`.

Use: a standalone supporting integrability result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_integrable` with the
arguments shown in the proof.
-/
theorem curveAmplitude_integrable (h w : SmoothTest) (t : ℝ) :
    Integrable (curveAmplitude h w t) :=
  (n_integrable.add (h.property.1.continuous.integrable_of_hasCompactSupport
    h.property.2 |>.const_mul t)).add
      (w.property.1.continuous.integrable_of_hasCompactSupport w.property.2 |>.const_mul _)

 /--
Exact identity `(∫ x, curveAmplitude h w t x)=1`.

Use: `chebyshev2.LocalObstruction.curveDensity_sqrt_mass` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), (∫
x, sqrt (curveDensity h w t x))=1`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_integrable`,
`chebyshev2.SineContinuum.sqrt_m`, `chebyshev2.SineContinuum.sqrt_mass` with the
arguments shown in the proof.
-/
theorem curveAmplitude_mass (h w : SmoothTest) (hh : (∫ x, h x)=0)
    (hw : (∫ x, w x)=0) (t : ℝ) : (∫ x, curveAmplitude h w t x)=1 := by
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => h x) := h.property.1.continuous.integrable_of_hasCompactSupport h.property.2
  -- Establish hj as the integrability justification for the later integral estimates or
  -- changes of order.
  have hj : Integrable (fun x => w x) := w.property.1.continuous.integrable_of_hasCompactSupport w.property.2
  unfold curveAmplitude
  have he₁ := integral_add (n_integrable.add (hi.const_mul t)) (hj.const_mul (curveCorrection h w t))
  have he₂ := integral_add n_integrable (hi.const_mul t)
  simp only [Pi.add_apply] at he₁ he₂
  rw [he₁,he₂,integral_const_mul,integral_const_mul,hh,hw]
  have hn : (∫ x, n x)=1 := by simpa only [sqrt_m] using sqrt_mass
  simp only [hn,mul_zero,add_zero]

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), (∫ x,
curveDensity h w t x)=1`.

Use: `chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient` uses this identity to
establish constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f
x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f
x))=1 ∧ (∀ x, |f x-m x|<ε) ∧ densityEnergy f<B f`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem curveDensity_mass (h w : SmoothTest) (hh : (∫ x, n x*h x)=0)
    (hw : 0<(∫ x, n x*w x)) : ∀ᶠ t in 𝓝 (0:ℝ), (∫ x, curveDensity h w t x)=1 := by
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => h x) := h.property.1.continuous.integrable_of_hasCompactSupport h.property.2
  -- Establish hsq as the integrability justification for the later integral estimates or
  -- changes of order.
  have hsq : Integrable (fun x => h x^2) := by
    simpa only [pow_two] using test_integrable h h.property.1.continuous
  -- Establish hnh as the integrability justification for the later integral estimates or
  -- changes of order.
  have hnh : Integrable (fun x => n x*h x) := by
    simpa only [mul_comm] using test_integrable h n_continuous
  -- Establish hbase as the integrability justification for the later integral estimates or
  -- changes of order.
  have hbase (t : ℝ) : Integrable (fun x => (n x+t*h x)^2) := by
    have he : (fun x => (n x+t*h x)^2)=fun x => n x^2+2*t*(n x*h x)+t^2*h x^2 := by
      funext x
      ring
    rw [he]
    exact (m_integrable.add (hnh.const_mul (2*t))).add (hsq.const_mul (t^2))
  filter_upwards [quadraticCorrection_equation
    (B := 2*∫ x, n x*w x) (C := ∫ x, h x*w x) (D := ∫ x, w x^2) (E := ∫ x, h x^2)
    (mul_pos (by norm_num) hw)] with t ht
  change t^2*(∫ x, h x^2)+curveCorrection h w t*(2*(∫ x, n x*w x)+2*t*(∫ x, h x*w x))+
    (∫ x, w x^2)*(curveCorrection h w t)^2=0 at ht
  have he : (∫ x, (n x+t*h x)*w x)=(∫ x, n x*w x)+t*(∫ x, h x*w x) := by
    simp only [add_mul,mul_assoc]
    rw [integral_add (by simpa only [mul_comm] using test_integrable w n_continuous)
      ((test_integrable h w.property.1.continuous).const_mul t),integral_const_mul]
  unfold curveDensity curveAmplitude
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : Continuous (fun x => n x+t*h x) :=
    n_continuous.add (continuous_const.mul h.property.1.continuous)
  rw [square_add_integral (f := fun x => n x+t*h x) hcont (hbase t) w (curveCorrection h w t),
    square_add_integral n_continuous m_integrable h t,he,hh]
  have hmass : (∫ x, n x^2)=1 := mass
  rw [hmass]
  nlinarith [ht]

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ (fun x => curveDensity h w t x-m x) ∧
HasCompactSupport (fun x => curveDensity h w t x-m x)`.

Use: `chebyshev2.LocalObstruction.curveDensity_integrable` uses this identity to establish
integrability of the displayed function: `Integrable (curveDensity h w t)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem curveDensity_increment (h w : SmoothTest) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => curveDensity h w t x-m x) ∧
    HasCompactSupport (fun x => curveDensity h w t x-m x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hd : ContDiff ℝ ∞ (fun x => t*h x+curveCorrection h w t*w x) :=
    (contDiff_const.mul h.property.1).add (contDiff_const.mul w.property.1)
  have hc : HasCompactSupport (fun x => t*h x+curveCorrection h w t*w x) :=
    h.property.2.mul_left.add w.property.2.mul_left
  refine ⟨(((n_smooth.add (contDiff_const.mul h.property.1)).add
    (contDiff_const.mul w.property.1)).pow 2).sub m_smooth,?_⟩
  have he : (fun x => curveDensity h w t x-m x)=fun x =>
      2*n x*(t*h x+curveCorrection h w t*w x)+(t*h x+curveCorrection h w t*w x)^2 := by
    funext x
    unfold curveDensity curveAmplitude m
    ring
  rw [he]
  exact hc.mul_left.add (hc.comp_left (g := fun z : ℝ => z^2) (by norm_num))

 /--
The actual derivative at the stated point: `HasDerivAt (fun t => curveDensity h w t x) (2*n x*h
x) 0`.

Use: `chebyshev2.LocalObstruction.sine_normalized_curve` uses this derivative formula to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.curveCorrection_derivative`,
`chebyshev2.LocalObstruction.curveCorrection_zero` with the arguments shown in the proof.
-/
theorem curveDensity_derivative (h w : SmoothTest) (hw : 0<(∫ x, n x*w x)) (x : ℝ) :
    HasDerivAt (fun t => curveDensity h w t x) (2*n x*h x) 0 := by
  have hd := (((hasDerivAt_const (0:ℝ) (n x)).add
    ((hasDerivAt_id (0:ℝ)).mul_const (h x))).add
      ((curveCorrection_derivative h w hw).mul_const (w x))).pow 2
  convert! hd using 1
  simp [Pi.add_apply,curveCorrection_zero]

end
end chebyshev2.LocalObstruction
