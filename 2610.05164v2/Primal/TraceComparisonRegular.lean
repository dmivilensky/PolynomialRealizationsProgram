import «2610.05164v2».Primal.ComparisonRegular

/-!
Article: 2610.05164v2, Proposition 13.
The exact square-trace comparison in regular cubic coordinates.
Use: `«2610.05164v2».Primal.trace_profile_difference_cubic` feeds
`«2610.05164v2».Primal.familySquareTrace_comparison` (family Square Trace comparison).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Real MeasureTheory «2610.05164v2».Filters «2610.05164v2».PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `actualRightLinear hψ κ (2-t^3)=linearFilter hψ κ t`.

Use: `«2610.05164v2».Primal.trace_difference_reflected_core_identity` rewrites with this
identity to establish `normalizedVelocity φ t*traceDifferenceDensity
hφ hψ κ (-normalizedX hφ t)= traceDifferenceReflectedCore hφ hψ κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem actualRightLinear_mirror_cubic {ψ : ℝ → ℝ} (hψ : Continuous ψ) (κ t : ℝ) :
    actualRightLinear hψ κ (2-t^3)=linearFilter hψ κ t := by
  have hsym : reflected ((speedData ψ hψ).density κ)=(speedData ψ hψ).density κ := by
    funext x
    exact density_reflection hψ κ x
  unfold actualRightLinear linearFilter normalizedX
  rw [hsym,X_reflection,neg_neg]

/--
Defines `traceDifferenceDensity` of type `ℝ` by `actualComparisonA0 hψ κ ((speedData φ hφ).q x)
(κ*causal 2 ((speedData φ hφ).density κ) x)* ((speedData φ hφ).density κ x-(amplitude ψ κ
((speedData φ hφ).q x))^2)`.

Use: `«2610.05164v2».Primal.traceDifferenceDensity_integrable` uses this definition to
establish integrability of the displayed function: `Integrable (traceDifferenceDensity hφ hψ
κ)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def traceDifferenceDensity {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (κ x : ℝ) : ℝ :=
  actualComparisonA0 hψ κ ((speedData φ hφ).q x)
    (κ*causal 2 ((speedData φ hφ).density κ) x)*
    ((speedData φ hφ).density κ x-(amplitude ψ κ ((speedData φ hφ).q x))^2)

/--
Defines `traceDifferenceCore` of type `ℝ` by `(3/2:ℝ)*exp (-ψ t)*(2*linearFilter hφ κ
t*reflectedLinearFilter hψ κ t- t^3*(2-t^3)*(linearFilter hφ κ t+reflectedLinearFilter hψ κ
t))*(1-exp (ψ t-φ t))`.

Use: `«2610.05164v2».Primal.trace_difference_core_identity` uses this definition to establish
the precise assertion is `normalizedVelocity φ t*traceDifferenceDensity hφ hψ κ (normalizedX hφ
t)= traceDifferenceCore hφ hψ κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def traceDifferenceCore {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (κ t : ℝ) : ℝ :=
  (3/2:ℝ)*exp (-ψ t)*(2*linearFilter hφ κ t*reflectedLinearFilter hψ κ t-
    t^3*(2-t^3)*(linearFilter hφ κ t+reflectedLinearFilter hψ κ t))*(1-exp (ψ t-φ t))

/--
Defines `traceDifferenceReflectedCore` of type `ℝ` by `(3/2:ℝ)*exp (-ψ
t)*(2*reflectedLinearFilter hφ κ t*linearFilter hψ κ t- t^3*(2-t^3)*(reflectedLinearFilter hφ κ
t+linearFilter hψ κ t))*(1-exp (ψ t-φ t))`.

Use: `«2610.05164v2».Primal.trace_difference_reflected_core_identity` uses this definition to
establish the precise assertion is `normalizedVelocity φ t*traceDifferenceDensity hφ hψ κ
(-normalizedX hφ t)= traceDifferenceReflectedCore hφ hψ κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def traceDifferenceReflectedCore {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (κ t : ℝ) : ℝ :=
  (3/2:ℝ)*exp (-ψ t)*(2*reflectedLinearFilter hφ κ t*linearFilter hψ κ t-
    t^3*(2-t^3)*(reflectedLinearFilter hφ κ t+linearFilter hψ κ t))*(1-exp (ψ t-φ t))

/--
Integrability of the displayed function: `Integrable (traceDifferenceDensity hφ hψ κ)`.

Use: `«2610.05164v2».Primal.trace_profile_difference_cubic` rewrites with this integrability
result to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».Comparison.Profile.comparisonA0_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density` with the arguments shown in
the proof.
-/
theorem traceDifferenceDensity_integrable {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ : ℝ} (hκ : 0<κ) :
    Integrable (traceDifferenceDensity hφ hψ κ) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».Comparison.Profile.comparisonA0_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density` with the arguments
  -- shown in the proof.
  let G := groundWitness hφ hκ
  have h := «2610.05164v2».Comparison.Profile.comparisonA0_integrable G
    (comparisonProfile hψ G.coupling_positive)
  rw [(speedData φ hφ).ground_coordinate hκ G,comparisonA0_eq] at h
  have hk := (speedData φ hφ).groundParameter_density hκ
  unfold traceDifferenceDensity
  simpa only [hk,comparisonProfile,«2610.05164v2».Filters.linear] using h

/--
Exact identity `traceDifferenceDensity hφ hψ κ x=0`.

Use: `«2610.05164v2».Primal.trace_profile_difference_cubic` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_zero_left` with
the arguments shown in the proof.
-/
theorem traceDifferenceDensity_zero_left {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (κ : ℝ) {x : ℝ}
    (hx : x≤(speedData φ hφ).X 0) : traceDifferenceDensity hφ hψ κ x=0 := by
  unfold traceDifferenceDensity actualComparisonA0
  rw [(speedData φ hφ).q_zero_left hx,ite_eq_right (by simp),zero_mul]

/--
Exact identity `traceDifferenceDensity hφ hψ κ x=0`.

Use: `«2610.05164v2».Primal.trace_profile_difference_cubic` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_two_right` with
the arguments shown in the proof.
-/
theorem traceDifferenceDensity_zero_right {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (κ : ℝ) {x : ℝ}
    (hx : (speedData φ hφ).X 2≤x) : traceDifferenceDensity hφ hψ κ x=0 := by
  unfold traceDifferenceDensity actualComparisonA0
  rw [(speedData φ hφ).q_two_right hx,ite_eq_right (by simp),zero_mul]

/--
The precise assertion is `normalizedVelocity φ t*traceDifferenceDensity hφ hψ κ (normalizedX hφ
t)= traceDifferenceCore hφ hψ κ t`.

Use: `«2610.05164v2».Primal.trace_profile_difference_cubic` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem trace_difference_core_identity {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) :
    normalizedVelocity φ t*traceDifferenceDensity hφ hψ κ (normalizedX hφ t)=
      traceDifferenceCore hφ hψ κ t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have ht3 : t^3≤1 := pow_le_one₀ ht'.1 ht'.2
  have hq : t^3∈Ioo (0:ℝ) 2 := ⟨pow_pos ht.1 _,by linarith⟩
  have hcoord : (speedData φ hφ).q (normalizedX hφ t)=t^3 :=
    (speedData φ hφ).q_X ⟨hq.1.le,hq.2.le⟩
  have hamp : (amplitude ψ κ (t^3))^2=(speed ψ (t^3)+t^3*(2-t^3))/κ := by
    have h := amplitude_square ψ hκ ⟨hq.1.le,hq.2.le⟩
    apply (eq_div_iff hκ.ne').mpr
    unfold «2610.05164v2».Calibration.Q at h
    linarith
  unfold traceDifferenceDensity
  rw [hcoord,actualComparisonA0,ite_eq_left hq,actualRightLinear_cubic,
    normalized_density hφ κ ht',hamp]
  change normalizedVelocity φ t*
    («2610.05164v2».Comparison.traceCoefficient κ (t^3) (speed ψ (t^3))
      (linearFilter hφ κ t) (reflectedLinearFilter hψ κ t)*
      ((t^2*exp (φ t)+t^3*(2-t^3))/κ-
        (speed ψ (t^3)+(t^3)*(2-t^3))/κ))=_
  simp only [speed_cubic ψ ht']
  unfold «2610.05164v2».Comparison.traceCoefficient «2610.05164v2».Calibration.Q traceDifferenceCore normalizedVelocity
  rw [exp_sub,exp_neg,exp_neg]
  field_simp [hκ.ne',ht.1.ne',exp_ne_zero]
  ring

/--
The precise assertion is `normalizedVelocity φ t*traceDifferenceDensity hφ hψ κ (-normalizedX
hφ t)= traceDifferenceReflectedCore hφ hψ κ t`.

Use: `«2610.05164v2».Primal.trace_profile_difference_cubic` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem trace_difference_reflected_core_identity {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) :
    normalizedVelocity φ t*traceDifferenceDensity hφ hψ κ (-normalizedX hφ t)=
      traceDifferenceReflectedCore hφ hψ κ t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have ht3 : t^3≤1 := pow_le_one₀ ht'.1 ht'.2
  have hq : 2-t^3∈Ioo (0:ℝ) 2 := ⟨by linarith,by linarith [pow_pos ht.1 3]⟩
  have hcoord : (speedData φ hφ).q (-normalizedX hφ t)=2-t^3 := by
    rw [inverse_reflection,normalizedX,(speedData φ hφ).q_X ⟨pow_nonneg ht'.1 _,ht3.trans (by norm_num)⟩]
  have hspeed : speed ψ (2-t^3)=t^2*exp (ψ t) := by
    calc
      speed ψ (2-t^3)=speed ψ (t^3) := by unfold speed;rw [coordinate_reflection]
      _=t^2*exp (ψ t) := speed_cubic ψ ht'
  have hamp : (amplitude ψ κ (2-t^3))^2=(t^2*exp (ψ t)+t^3*(2-t^3))/κ := by
    have h := amplitude_square ψ hκ ⟨hq.1.le,hq.2.le⟩
    rw [hspeed] at h
    apply (eq_div_iff hκ.ne').mpr
    unfold «2610.05164v2».Calibration.Q at h
    nlinarith only [h]
  have hfilter : κ*causal 2 ((speedData φ hφ).density κ) (-normalizedX hφ t)=
      reflectedLinearFilter hφ κ t := by
    unfold normalizedX reflectedLinearFilter reflectedX
    rw [X_reflection]
  unfold traceDifferenceDensity
  rw [hcoord,actualComparisonA0,ite_eq_left hq,actualRightLinear_mirror_cubic,
    density_reflection,normalized_density hφ κ ht',hamp,hfilter,hspeed]
  unfold «2610.05164v2».Comparison.traceCoefficient «2610.05164v2».Calibration.Q traceDifferenceReflectedCore normalizedVelocity
  rw [exp_sub,exp_neg,exp_neg]
  field_simp [hκ.ne',ht.1.ne',exp_ne_zero]
  ring

/--
The precise assertion is `(∫ x,(κ*causal 2 ((speedData φ hφ).density κ) x)^2)- (∫ x,(κ*causal 2
((speedData ψ hψ).density κ) x)^2)= ∫ t in (0:ℝ)..1,traceDifferenceCore hφ hψ κ
t+traceDifferenceReflectedCore hφ hψ κ t`.

Use: `«2610.05164v2».Primal.familySquareTrace_comparison` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.trace_profile_difference`,
`«2610.05164v2».Primal.full_integral_cubic`,
`«2610.05164v2».Primal.traceDifferenceDensity_integrable` with the arguments shown in the
proof.
-/
theorem trace_profile_difference_cubic {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ : ℝ} (hκ : 0<κ) :
    (∫ x,(κ*causal 2 ((speedData φ hφ).density κ) x)^2)-
    (∫ x,(κ*causal 2 ((speedData ψ hψ).density κ) x)^2)=
    ∫ t in (0:ℝ)..1,traceDifferenceCore hφ hψ κ t+traceDifferenceReflectedCore hφ hψ κ t := by
  -- Use the identities/estimates `«2610.05164v2».Primal.trace_profile_difference`,
  -- `«2610.05164v2».Primal.full_integral_cubic`,
  -- `«2610.05164v2».Primal.traceDifferenceDensity_integrable` with the arguments shown in the
  -- proof.
  rw [trace_profile_difference hφ hψ hκ]
  change (∫ x,traceDifferenceDensity hφ hψ κ x)=_
  rw [full_integral_cubic hφ (traceDifferenceDensity_integrable hφ hψ hκ)
    (fun x hx => traceDifferenceDensity_zero_left hφ hψ κ hx)
    (fun x hx => traceDifferenceDensity_zero_right hφ hψ κ hx)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  rcases eq_or_lt_of_le ht'.1 with he|hp
  · subst t
    have hX : -(speedData φ hφ).X 0=(speedData φ hφ).X 2 := by
      simpa only [sub_zero] using (X_reflection hφ 0).symm
    simp only [normalizedX,zero_pow (by decide : 3≠0),hX,
      traceDifferenceDensity_zero_left hφ hψ κ le_rfl,
      traceDifferenceDensity_zero_right hφ hψ κ le_rfl]
    simp [traceDifferenceCore,traceDifferenceReflectedCore,linearFilter_initial]
  · dsimp only
    rw [mul_add,trace_difference_core_identity hφ hψ hκ ⟨hp,ht'.2⟩,
      trace_difference_reflected_core_identity hφ hψ hκ ⟨hp,ht'.2⟩]

end
end «2610.05164v2».Primal
