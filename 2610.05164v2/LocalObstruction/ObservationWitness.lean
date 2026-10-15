import «2610.05164v2».LocalObstruction.VariationalObstruction

/-!
Article: 2610.05164v2, Theorem 6.1.
A checked observation consists of finite-family regularity and its actual first variation.
Use: `«2610.05164v2».LocalObstruction.ObservationWitness.curve_derivative` feeds
`«2610.05164v2».LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».SineContinuum Asymptotics
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
An observation gradient/tail witness, with actual C¹ regularity on smooth perturbation families
and the directional-derivative pairing formula. The tail information drives the finite-
observation local obstruction.

Use: `«2610.05164v2».LocalObstruction.ObservationWitness.curve_derivative` uses this record of
data and proof obligations to establish the actual derivative at the stated point: `HasDerivAt
(fun t => O (curveDensity (amplitudeDirection v) w t)) (∫ x,v x*W.gradient.value x) 0`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
structure TailGradient where
  /-- Continuous observation-gradient tail profile. -/
  value : ℝ → ℝ
  /-- Continuity of the tail profile on the real line. -/
  continuous : Continuous value
  /-- Constant asymptotic component of the observation gradient. -/
  constant : ℝ
  /-- Coefficient of its leading exp(-2x) tail component. -/
  exponential : ℝ
  /-- After subtracting the leading two components, the remainder is little-o of the comparison tail n. -/
  tail : (fun x => value x-constant-exponential*exp (-2*x)) =o[atTop] n

 /--
An observation gradient/tail witness, with actual C¹ regularity on smooth perturbation families
and the directional-derivative pairing formula. The tail information drives the finite-
observation local obstruction.

Use: `«2610.05164v2».LocalObstruction.ObservationWitness.curve_derivative` uses this record of
data and proof obligations to establish the actual derivative at the stated point: `HasDerivAt
(fun t => O (curveDensity (amplitudeDirection v) w t)) (∫ x,v x*W.gradient.value x) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
structure ObservationWitness (O : (ℝ → ℝ) → ℝ) where
  /-- Gradient representation used to pair an observation derivative with a smooth perturbation. -/
  gradient : TailGradient
  /-- C¹ regularity of the observation on every five-parameter smooth perturbation family. -/
  regular : ∀ h w : SmoothTest, ContDiffAt ℝ 1
    (fun a : Fin 5 → ℝ => O (perturb m (fun i x => curveBasis h w i x) a)) 0
  /-- Actual directional derivative equals integration against the gradient; this links the tail obstruction to finite-dimensional perturbations. -/
  variation : ∀ v : SmoothTest, HasDerivAt (fun ε : ℝ => O (m+ε • (v:ℝ → ℝ)))
    (∫ x,v x*gradient.value x) 0

 /--
The stated quantitative bound `perturb m (fun i x => curveBasis (amplitudeDirection v) w i x)
(ε • curveTangent)= m+ε • (v:ℝ → ℝ)`.

Use: `«2610.05164v2».LocalObstruction.ObservationWitness.curve_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun t => O
(curveDensity (amplitudeDirection v) w t)) (∫ x,v x*W.gradient.value x) 0`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem curve_first_direction (v w : SmoothTest) (ε : ℝ) :
    perturb m (fun i x => curveBasis (amplitudeDirection v) w i x) (ε • curveTangent)=
      m+ε • (v:ℝ → ℝ) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  funext x
  simp only [perturb,Fin.sum_univ_succ,Fin.sum_univ_zero,curveBasis,curveTangent,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Pi.smul_apply,smul_eq_mul,
    mul_one,mul_zero,zero_mul,add_zero,Pi.add_apply]
  change m x+ε*(2*n x*(v x/(2*n x)))=m x+ε*v x
  field_simp [(n_positive x).ne']

 /--
The actual derivative at the stated point: `HasDerivAt (fun t => O (curveDensity
(amplitudeDirection v) w t)) (∫ x,v x*W.gradient.value x) 0`.

Use: `«2610.05164v2».LocalObstruction.finite_observation_no_local_bound_with_property` uses
this derivative formula to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ObservationWitness.curve_derivative {O : (ℝ → ℝ) → ℝ} (W : ObservationWitness O)
    (v w : SmoothTest) (hw : 0<∫ x,n x*w x) :
    HasDerivAt (fun t => O (curveDensity (amplitudeDirection v) w t))
      (∫ x,v x*W.gradient.value x) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let f := fun a : Fin 5 → ℝ => O (perturb m (fun i x => curveBasis (amplitudeDirection v) w i x) a)
  have hD : DifferentiableAt ℝ f 0 :=
    (W.regular (amplitudeDirection v) w).differentiableAt (by norm_num : (1:ℕ∞ω)≠0)
  have hline : HasDerivAt (fun ε : ℝ => ε • curveTangent) curveTangent 0 := by
    convert! (hasDerivAt_id (0:ℝ)).smul_const curveTangent using 1
    simp
  have hD' : HasFDerivAt f (fderiv ℝ f 0) ((0:ℝ) • curveTangent) := by
    simpa only [zero_smul] using hD.hasFDerivAt
  have ht := hD'.comp_hasDerivAt (0:ℝ) hline
  have ht' : HasDerivAt (fun ε : ℝ => O (m+ε • (v:ℝ → ℝ))) (fderiv ℝ f 0 curveTangent) 0 := by
    convert! ht using 1
    funext ε
    dsimp only [Function.comp_def,f]
    rw [curve_first_direction]
  have hv := ht'.unique (W.variation v)
  rw [← hv]
  exact finite_observation_curve_derivative O (amplitudeDirection v) w hw _ hD.hasFDerivAt

end
end «2610.05164v2».LocalObstruction
