import chebyshev2.LocalObstruction.EnergyVariation

/-!
Article: chebyshev2, Theorem 6.1.
A fixed five-dimensional family contains the entire nonlinear normalized curve.
Use: `chebyshev2.LocalObstruction.finite_observation_curve_derivative` feeds
`chebyshev2.LocalObstruction.ObservationWitness.curve_derivative` (curve derivative).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory chebyshev2.SineContinuum
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `curveBasis` of type `Fin 5 → SmoothTest`. The displayed construction fixes its
component data; its proof fields enforce the listed compatibility properties.

Use: `chebyshev2.LocalObstruction.curveDensity_eq_perturb` rewrites with this definition to
establish exact identity `curveDensity h w t=perturb m (fun i x => curveBasis h w i x)
(curveParameters h w t)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def curveBasis (h w : SmoothTest) : Fin 5 → SmoothTest :=
  ![⟨fun x => 2*n x*h x,(contDiff_const.mul n_smooth).mul h.property.1,h.property.2.mul_left⟩,
    ⟨fun x => 2*n x*w x,(contDiff_const.mul n_smooth).mul w.property.1,w.property.2.mul_left⟩,
    ⟨fun x => h x^2,h.property.1.pow 2,h.property.2.comp_left (g := fun z : ℝ => z^2) (by norm_num)⟩,
    ⟨fun x => 2*h x*w x,(contDiff_const.mul h.property.1).mul w.property.1,w.property.2.mul_left⟩,
    ⟨fun x => w x^2,w.property.1.pow 2,w.property.2.comp_left (g := fun z : ℝ => z^2) (by norm_num)⟩]

/--
Defines `curveParameters` of type `Fin 5 → ℝ` by `![t,curveCorrection h w
t,t^2,t*curveCorrection h w t,(curveCorrection h w t)^2]`.

Use: `chebyshev2.LocalObstruction.curveDensity_eq_perturb` rewrites with this definition to
establish exact identity `curveDensity h w t=perturb m (fun i x => curveBasis h w i x)
(curveParameters h w t)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def curveParameters (h w : SmoothTest) (t : ℝ) : Fin 5 → ℝ :=
  ![t,curveCorrection h w t,t^2,t*curveCorrection h w t,(curveCorrection h w t)^2]

/--
Defines `curveTangent` of type `Fin 5 → ℝ` by `![1,0,0,0,0]`.

Use: `chebyshev2.LocalObstruction.curveParameters_derivative` rewrites with this definition
to establish the actual derivative at the stated point: `HasDerivAt (curveParameters h w)
curveTangent 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def curveTangent : Fin 5 → ℝ := ![1,0,0,0,0]

/--
Exact identity `curveParameters h w 0=0`.

Use: `chebyshev2.LocalObstruction.finite_observation_curve_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun t => O
(curveDensity h w t)) (L curveTangent) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem curveParameters_zero (h w : SmoothTest) : curveParameters h w 0=0 := by
  ext i
  fin_cases i <;> simp [curveParameters,curveCorrection_zero]

/--
The actual derivative at the stated point: `HasDerivAt (curveParameters h w) curveTangent 0`.

Use: `chebyshev2.LocalObstruction.finite_observation_curve_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun t => O
(curveDensity h w t)) (L curveTangent) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem curveParameters_derivative (h w : SmoothTest) (hw : 0<(∫ x, n x*w x)) :
    HasDerivAt (curveParameters h w) curveTangent 0 := by
  -- Check each member of the finite index type; no case is omitted.
  apply hasDerivAt_pi.mpr
  intro i
  have ht := hasDerivAt_id (0:ℝ)
  have ha := curveCorrection_derivative h w hw
  fin_cases i
  · convert! ht using 1
  · simpa [curveParameters,curveTangent] using ha
  · convert! ht.pow 2 using 1
    norm_num [curveParameters,curveTangent]
  · convert! ht.mul ha using 1
    simp [curveTangent,curveCorrection_zero]
  · convert! ha.pow 2 using 1
    simp [curveTangent,curveCorrection_zero]

/--
Smoothness to the stated order: `ContDiffAt ℝ ∞ (curveParameters h w) 0`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem curveParameters_smooth (h w : SmoothTest) (hw : 0<(∫ x, n x*w x)) :
    ContDiffAt ℝ ∞ (curveParameters h w) 0 := by
  -- Check each member of the finite index type; no case is omitted.
  have ha : ContDiffAt ℝ ∞ (curveCorrection h w) 0 :=
    quadraticCorrection_smooth (mul_pos (by norm_num) hw)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_id
  · exact ha
  · exact contDiffAt_id.pow 2
  · exact contDiffAt_id.mul ha
  · exact ha.pow 2

/--
Exact identity `curveDensity h w t=perturb m (fun i x => curveBasis h w i x) (curveParameters h
w t)`.

Use: `chebyshev2.LocalObstruction.finite_observation_curve_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun t => O
(curveDensity h w t)) (L curveTangent) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem curveDensity_eq_perturb (h w : SmoothTest) (t : ℝ) :
    curveDensity h w t=perturb m (fun i x => curveBasis h w i x) (curveParameters h w t) := by
  funext x
  simp only [perturb,Fin.sum_univ_succ,Fin.sum_univ_zero,
    curveBasis,curveParameters,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,
    curveDensity,curveAmplitude,m]
  ring

/--
The actual derivative at the stated point: `HasDerivAt (fun t => O (curveDensity h w t)) (L
curveTangent) 0`.

Use: `chebyshev2.LocalObstruction.ObservationWitness.curve_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun t => O
(curveDensity (amplitudeDirection v) w t)) (∫ x,v x*W.gradient.value x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem finite_observation_curve_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (O : (ℝ → ℝ) → E) (h w : SmoothTest)
    (hw : 0<(∫ x, n x*w x)) (L : (Fin 5 → ℝ) →L[ℝ] E)
    (hO : HasFDerivAt (fun a => O (perturb m (fun i x => curveBasis h w i x) a)) L 0) :
    HasDerivAt (fun t => O (curveDensity h w t)) (L curveTangent) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hObs := hO
  rw [← curveParameters_zero h w] at hObs
  have he := hObs.comp_hasDerivAt 0 (curveParameters_derivative h w hw)
  convert! he using 1
  funext t
  rw [Function.comp_apply,curveDensity_eq_perturb]

end
end chebyshev2.LocalObstruction
