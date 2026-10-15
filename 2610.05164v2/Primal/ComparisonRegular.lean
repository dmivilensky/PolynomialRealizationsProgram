import «2610.05164v2».Primal.ComparisonDifference
import «2610.05164v2».Primal.Observations

/-!
Article: 2610.05164v2, Proposition 13.
Regular cubic-coordinate kernels for the exact finite comparison of two primal profiles.
Use: `«2610.05164v2».Primal.determinant_profile_difference_cubic` feeds
`«2610.05164v2».Primal.familyLogDeterminant_comparison` (family Log Determinant comparison).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Real MeasureTheory «2610.05164v2».Filters «2610.05164v2».PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `actualRightFilter hψ κ s (t^3)=reflectedNonlinearFilter hψ κ s t`.

Use: `«2610.05164v2».Primal.determinant_difference_core_identity` rewrites with this identity
to establish `normalizedVelocity φ t*determinantDifferenceDensity hφ
hψ κ s (normalizedX hφ t)= determinantDifferenceCore hφ hψ κ s t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem actualRightFilter_cubic {ψ : ℝ → ℝ} (hψ : Continuous ψ) (κ s t : ℝ) :
    actualRightFilter hψ κ s (t^3)=reflectedNonlinearFilter hψ κ s t := by
  have hsym : reflected ((speedData ψ hψ).density κ)=(speedData ψ hψ).density κ := by
    funext x
    exact density_reflection hψ κ x
  unfold actualRightFilter reflectedNonlinearFilter reflectedX
  rw [hsym,← X_reflection hψ (t^3)]

/--
Exact identity `actualRightLinear hψ κ (t^3)=reflectedLinearFilter hψ κ t`.

Use: `«2610.05164v2».Primal.trace_difference_core_identity` rewrites with this identity to
establish the precise assertion is `normalizedVelocity φ t*traceDifferenceDensity hφ hψ κ
(normalizedX hφ t)= traceDifferenceCore hφ hψ κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem actualRightLinear_cubic {ψ : ℝ → ℝ} (hψ : Continuous ψ) (κ t : ℝ) :
    actualRightLinear hψ κ (t^3)=reflectedLinearFilter hψ κ t := by
  have hsym : reflected ((speedData ψ hψ).density κ)=(speedData ψ hψ).density κ := by
    funext x
    exact density_reflection hψ κ x
  unfold actualRightLinear reflectedLinearFilter reflectedX
  rw [hsym,← X_reflection hψ (t^3)]

/--
Exact identity `actualRightFilter hψ κ s (2-t^3)=nonlinearFilter hψ κ s t`.

Use: `«2610.05164v2».Primal.determinant_difference_reflected_core_identity` rewrites with this
identity to establish `normalizedVelocity φ
t*determinantDifferenceDensity hφ hψ κ s (-normalizedX hφ t)=
determinantDifferenceReflectedCore hφ hψ κ s t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem actualRightFilter_mirror_cubic {ψ : ℝ → ℝ} (hψ : Continuous ψ) (κ s t : ℝ) :
    actualRightFilter hψ κ s (2-t^3)=nonlinearFilter hψ κ s t := by
  have hsym : reflected ((speedData ψ hψ).density κ)=(speedData ψ hψ).density κ := by
    funext x
    exact density_reflection hψ κ x
  unfold actualRightFilter nonlinearFilter normalizedX
  rw [hsym,X_reflection,neg_neg]

/--
Defines `determinantDifferenceDensity` of type `ℝ` by `actualComparisonA hψ κ s ((speedData φ
hφ).q x) (nonlinear s ((speedData φ hφ).density κ) x)* ((speedData φ hφ).density κ x-(amplitude
ψ κ ((speedData φ hφ).q x))^2)`.

Use: `«2610.05164v2».Primal.determinantDifferenceDensity_integrable` uses this definition to
establish integrability of the displayed function: `Integrable (determinantDifferenceDensity hφ
hψ κ s)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def determinantDifferenceDensity {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (κ s x : ℝ) : ℝ :=
  actualComparisonA hψ κ s ((speedData φ hφ).q x)
    (nonlinear s ((speedData φ hφ).density κ) x)*
    ((speedData φ hφ).density κ x-(amplitude ψ κ ((speedData φ hφ).q x))^2)

/--
Defines `determinantDifferenceCore` of type `ℝ` by `-3*exp (-ψ t)*(s*t^3*(2-t^3)/κ+
nonlinearFilter hφ κ s t*reflectedNonlinearFilter hψ κ s t)/ (2+nonlinearFilter hφ κ s
t+reflectedNonlinearFilter hψ κ s t)* (1-exp (ψ t-φ t))`.

Use: `«2610.05164v2».Primal.determinant_difference_core_identity` uses this definition to
establish the precise assertion is `normalizedVelocity φ t*determinantDifferenceDensity hφ hψ κ
s (normalizedX hφ t)= determinantDifferenceCore hφ hψ κ s t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def determinantDifferenceCore {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (κ s t : ℝ) : ℝ :=
  -3*exp (-ψ t)*(s*t^3*(2-t^3)/κ+
    nonlinearFilter hφ κ s t*reflectedNonlinearFilter hψ κ s t)/
    (2+nonlinearFilter hφ κ s t+reflectedNonlinearFilter hψ κ s t)*
    (1-exp (ψ t-φ t))

/--
Defines `determinantDifferenceReflectedCore` of type `ℝ` by `-3*exp (-ψ t)*(s*t^3*(2-t^3)/κ+
reflectedNonlinearFilter hφ κ s t*nonlinearFilter hψ κ s t)/ (2+reflectedNonlinearFilter hφ κ s
t+nonlinearFilter hψ κ s t)* (1-exp (ψ t-φ t))`.

Use: `«2610.05164v2».Primal.determinant_difference_reflected_core_identity` uses this
definition to establish `normalizedVelocity φ
t*determinantDifferenceDensity hφ hψ κ s (-normalizedX hφ t)=
determinantDifferenceReflectedCore hφ hψ κ s t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def determinantDifferenceReflectedCore {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (κ s t : ℝ) : ℝ :=
  -3*exp (-ψ t)*(s*t^3*(2-t^3)/κ+
    reflectedNonlinearFilter hφ κ s t*nonlinearFilter hψ κ s t)/
    (2+reflectedNonlinearFilter hφ κ s t+nonlinearFilter hψ κ s t)*
    (1-exp (ψ t-φ t))

/--
Integrability of the displayed function: `Integrable (determinantDifferenceDensity hφ hψ κ s)`.

Use: `«2610.05164v2».Primal.determinant_profile_difference_cubic` rewrites with this
integrability result to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».Comparison.Profile.comparisonA_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density` with the arguments shown in
the proof.
-/
theorem determinantDifferenceDensity_integrable {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) :
    Integrable (determinantDifferenceDensity hφ hψ κ s) := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
  -- `«2610.05164v2».Comparison.Profile.comparisonA_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.groundParameter_density` with the arguments
  -- shown in the proof.
  let G := groundWitness hφ hκ
  have h := «2610.05164v2».Comparison.Profile.comparisonA_integrable G
    (comparisonProfile hψ G.coupling_positive) hs
  rw [(speedData φ hφ).ground_coordinate hκ G,comparisonA_eq] at h
  have hk := (speedData φ hφ).groundParameter_density hκ
  unfold determinantDifferenceDensity
  simpa only [hk,comparisonProfile] using h

/--
Exact identity `determinantDifferenceDensity hφ hψ κ s x=0`.

Use: `«2610.05164v2».Primal.determinant_profile_difference_cubic` rewrites with this identity
to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_zero_left` with
the arguments shown in the proof.
-/
theorem determinantDifferenceDensity_zero_left {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (κ s : ℝ) {x : ℝ}
    (hx : x≤(speedData φ hφ).X 0) : determinantDifferenceDensity hφ hψ κ s x=0 := by
  unfold determinantDifferenceDensity actualComparisonA
  rw [(speedData φ hφ).q_zero_left hx,ite_eq_right (by simp),zero_mul]

/--
Exact identity `determinantDifferenceDensity hφ hψ κ s x=0`.

Use: `«2610.05164v2».Primal.determinant_profile_difference_cubic` rewrites with this identity
to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_two_right` with
the arguments shown in the proof.
-/
theorem determinantDifferenceDensity_zero_right {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (κ s : ℝ) {x : ℝ}
    (hx : (speedData φ hφ).X 2≤x) : determinantDifferenceDensity hφ hψ κ s x=0 := by
  unfold determinantDifferenceDensity actualComparisonA
  rw [(speedData φ hφ).q_two_right hx,ite_eq_right (by simp),zero_mul]

/--
The precise assertion is `normalizedVelocity φ t*determinantDifferenceDensity hφ hψ κ s
(normalizedX hφ t)= determinantDifferenceCore hφ hψ κ s t`.

Use: `«2610.05164v2».Primal.determinant_profile_difference_cubic` rewrites with this identity
to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem determinant_difference_core_identity {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s t : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (ht : t∈Ioc (0:ℝ) 1) :
    normalizedVelocity φ t*determinantDifferenceDensity hφ hψ κ s (normalizedX hφ t)=
      determinantDifferenceCore hφ hψ κ s t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have ht3 : t^3≤1 := pow_le_one₀ ht'.1 ht'.2
  have hq : t^3∈Ioo (0:ℝ) 2 := ⟨pow_pos ht.1 _,by linarith⟩
  have hcoord : (speedData φ hφ).q (normalizedX hφ t)=t^3 :=
    (speedData φ hφ).q_X ⟨hq.1.le,hq.2.le⟩
  have hden : 0<2+nonlinearFilter hφ κ s t+reflectedNonlinearFilter hψ κ s t := by
    linarith [nonlinearFilter_nonneg hφ hκ hs t,reflectedNonlinearFilter_nonneg hψ hκ hs t]
  have hamp : (amplitude ψ κ (t^3))^2=(speed ψ (t^3)+t^3*(2-t^3))/κ := by
    have h := amplitude_square ψ hκ ⟨hq.1.le,hq.2.le⟩
    apply (eq_div_iff hκ.ne').mpr
    unfold «2610.05164v2».Calibration.Q at h
    linarith
  unfold determinantDifferenceDensity
  rw [hcoord,actualComparisonA,ite_eq_left hq,actualRightFilter_cubic,
    normalized_density hφ κ ht',hamp]
  change normalizedVelocity φ t*
    («2610.05164v2».Comparison.determinantCoefficient κ s (t^3) (speed ψ (t^3))
      (nonlinearFilter hφ κ s t) (reflectedNonlinearFilter hψ κ s t)*
      ((t^2*exp (φ t)+t^3*(2-t^3))/κ-
        (speed ψ (t^3)+(t^3)*(2-t^3))/κ))=_
  simp only [speed_cubic ψ ht']
  unfold «2610.05164v2».Comparison.determinantCoefficient «2610.05164v2».Calibration.Q determinantDifferenceCore normalizedVelocity
  rw [exp_sub,exp_neg,exp_neg]
  field_simp [hκ.ne',ht.1.ne',hden.ne',exp_ne_zero]
  ring

/--
The precise assertion is `normalizedVelocity φ t*determinantDifferenceDensity hφ hψ κ s
(-normalizedX hφ t)= determinantDifferenceReflectedCore hφ hψ κ s t`.

Use: `«2610.05164v2».Primal.determinant_profile_difference_cubic` rewrites with this identity
to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem determinant_difference_reflected_core_identity {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s t : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (ht : t∈Ioc (0:ℝ) 1) :
    normalizedVelocity φ t*determinantDifferenceDensity hφ hψ κ s (-normalizedX hφ t)=
      determinantDifferenceReflectedCore hφ hψ κ s t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have ht3 : t^3≤1 := pow_le_one₀ ht'.1 ht'.2
  have hq : 2-t^3∈Ioo (0:ℝ) 2 := ⟨by linarith,by linarith [pow_pos ht.1 3]⟩
  have hcoord : (speedData φ hφ).q (-normalizedX hφ t)=2-t^3 := by
    rw [inverse_reflection,normalizedX,(speedData φ hφ).q_X ⟨pow_nonneg ht'.1 _,ht3.trans (by norm_num)⟩]
  have hden : 0<2+reflectedNonlinearFilter hφ κ s t+nonlinearFilter hψ κ s t := by
    linarith [reflectedNonlinearFilter_nonneg hφ hκ hs t,nonlinearFilter_nonneg hψ hκ hs t]
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
  have hfilter : nonlinear s ((speedData φ hφ).density κ) (-normalizedX hφ t)=
      reflectedNonlinearFilter hφ κ s t := by
    unfold normalizedX reflectedNonlinearFilter reflectedX
    rw [X_reflection]
  unfold determinantDifferenceDensity
  rw [hcoord,actualComparisonA,ite_eq_left hq,actualRightFilter_mirror_cubic,
    density_reflection,normalized_density hφ κ ht',hamp,hfilter,hspeed]
  unfold «2610.05164v2».Comparison.determinantCoefficient «2610.05164v2».Calibration.Q
    determinantDifferenceReflectedCore normalizedVelocity
  rw [exp_sub,exp_neg,exp_neg]
  field_simp [hκ.ne',ht.1.ne',hden.ne',exp_ne_zero]
  ring

/--
The precise assertion is `«2610.05164v2».Continuum.logDeterminant
(«2610.05164v2».Continuum.kernelEigenvalue ((speedData φ hφ).density_integrable hκ) ((speedData
φ hφ).density_nonneg hκ)) s- «2610.05164v2».Continuum.logDeterminant
(«2610.05164v2».Continuum.kernelEigenvalue ((speedData ψ hψ).density_integrable hκ) ((speedData
ψ hψ).density_nonneg hκ)) s= ∫ t in (0:ℝ)..1,determinantDifferenceCore hφ hψ κ s t+
determinantDifferenceReflectedCore hφ hψ κ s t`.

Use: `«2610.05164v2».Primal.familyLogDeterminant_comparison` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.determinant_profile_difference`,
`«2610.05164v2».Primal.full_integral_cubic`,
`«2610.05164v2».Primal.determinantDifferenceDensity_integrable` with the arguments shown in the
proof.
-/
theorem determinant_profile_difference_cubic {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) :
    «2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue
      ((speedData φ hφ).density_integrable hκ) ((speedData φ hφ).density_nonneg hκ)) s-
    «2610.05164v2».Continuum.logDeterminant («2610.05164v2».Continuum.kernelEigenvalue
      ((speedData ψ hψ).density_integrable hκ) ((speedData ψ hψ).density_nonneg hκ)) s=
    ∫ t in (0:ℝ)..1,determinantDifferenceCore hφ hψ κ s t+
      determinantDifferenceReflectedCore hφ hψ κ s t := by
  -- Use the identities/estimates `«2610.05164v2».Primal.determinant_profile_difference`,
  -- `«2610.05164v2».Primal.full_integral_cubic`,
  -- `«2610.05164v2».Primal.determinantDifferenceDensity_integrable` with the arguments shown
  -- in the proof.
  rw [determinant_profile_difference hφ hψ hκ hs]
  change (∫ x,determinantDifferenceDensity hφ hψ κ s x)=_
  rw [full_integral_cubic hφ (determinantDifferenceDensity_integrable hφ hψ hκ hs)
    (fun x hx => determinantDifferenceDensity_zero_left hφ hψ κ s hx)
    (fun x hx => determinantDifferenceDensity_zero_right hφ hψ κ s hx)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  rcases eq_or_lt_of_le ht'.1 with he|hp
  · subst t
    have hX : -(speedData φ hφ).X 0=(speedData φ hφ).X 2 := by
      simpa only [sub_zero] using (X_reflection hφ 0).symm
    simp only [normalizedX,zero_pow (by decide : 3≠0),hX,
      determinantDifferenceDensity_zero_left hφ hψ κ s le_rfl,
      determinantDifferenceDensity_zero_right hφ hψ κ s le_rfl]
    simp [determinantDifferenceCore,determinantDifferenceReflectedCore,nonlinearFilter_initial]
  · dsimp only
    rw [mul_add,determinant_difference_core_identity hφ hψ hκ hs ⟨hp,ht'.2⟩,
      determinant_difference_reflected_core_identity hφ hψ hκ hs ⟨hp,ht'.2⟩]

end
end «2610.05164v2».Primal
