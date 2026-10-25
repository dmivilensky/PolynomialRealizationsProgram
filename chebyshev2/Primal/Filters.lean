import chebyshev2.Primal.FilterCoordinates

/-!
Article: chebyshev2, Proposition 13.
Filters.
Use: `chebyshev2.Primal.reflectedLinearFilter_ode` feeds
`chebyshev2.Primal.rightLinearFilter_regular_ode` (right Linear Filter regular ode).
Proof chain: `chebyshev2.Primal.familyConstraintMap_c1` — chebyshev2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace chebyshev2.Primal
noncomputable section
open Set MeasureTheory Real chebyshev2.PrescribedSpeed chebyshev2.Filters
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `normalizedDensity` of type `ℝ` by `(t^2*exp (φ t)+t^3*(2-t^3))/κ`.

Use: `chebyshev2.Primal.linearFilter_ode` uses this definition to establish the derivative
within the stated domain: `HasDerivWithinAt (linearFilter hφ κ) (normalizedVelocity φ
t*(κ*normalizedDensity φ κ t-2*linearFilter hφ κ t)) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def normalizedDensity (φ : ℝ → ℝ) (κ t : ℝ) : ℝ :=
  (t^2*exp (φ t)+t^3*(2-t^3))/κ
/--
Defines `nonlinearFilter` of type `ℝ` by `nonlinear s ((speedData φ hφ).density κ) (normalizedX
hφ t)`.

Use: `chebyshev2.Primal.nonlinearFilter_join` uses this definition to establish exact
identity `nonlinearFilter hφ κ s 1=reflectedNonlinearFilter hφ κ s 1`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.
-/
def nonlinearFilter {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s t : ℝ) : ℝ :=
  nonlinear s ((speedData φ hφ).density κ) (normalizedX hφ t)
/--
Defines `reflectedNonlinearFilter` of type `ℝ` by `nonlinear s ((speedData φ hφ).density κ)
(reflectedX hφ t)`.

Use: `chebyshev2.Primal.nonlinearFilter_join` uses this definition to establish exact
identity `nonlinearFilter hφ κ s 1=reflectedNonlinearFilter hφ κ s 1`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def reflectedNonlinearFilter {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s t : ℝ) : ℝ :=
  nonlinear s ((speedData φ hφ).density κ) (reflectedX hφ t)
/--
Defines `linearFilter` of type `ℝ` by `κ*causal 2 ((speedData φ hφ).density κ) (normalizedX hφ
t)`.

Use: `chebyshev2.Primal.linearFilter_initial` uses this definition to establish exact
identity `linearFilter hφ κ 0=0`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.square_trace_cubic`.
-/
def linearFilter {φ : ℝ → ℝ} (hφ : Continuous φ) (κ t : ℝ) : ℝ :=
  κ*causal 2 ((speedData φ hφ).density κ) (normalizedX hφ t)
/--
Defines `reflectedLinearFilter` of type `ℝ` by `κ*causal 2 ((speedData φ hφ).density κ)
(reflectedX hφ t)`.

Use: `chebyshev2.Primal.linearFilter_join` uses this definition to establish the identity
`linearFilter hφ κ 1=reflectedLinearFilter hφ κ 1`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def reflectedLinearFilter {φ : ℝ → ℝ} (hφ : Continuous φ) (κ t : ℝ) : ℝ :=
  κ*causal 2 ((speedData φ hφ).density κ) (reflectedX hφ t)

/--
Continuity of the displayed function: `Continuous (nonlinearFilter hφ κ s)`.

Use: `chebyshev2.Primal.familyNonlinearFilter_joint_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (familyNonlinearFilter hψ hθ κ s
reflected).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem nonlinearFilter_continuous {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) : Continuous (nonlinearFilter hφ κ s) :=
  (nonlinear_continuous ((speedData φ hφ).density_integrable hκ)
    ((speedData φ hφ).density_nonneg hκ) hs).comp (normalizedX_continuous hφ)
/--
Continuity of the displayed function: `Continuous (reflectedNonlinearFilter hφ κ s)`.

Use: `chebyshev2.Primal.familyNonlinearFilter_joint_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (familyNonlinearFilter hψ hθ κ s
reflected).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem reflectedNonlinearFilter_continuous {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) : Continuous (reflectedNonlinearFilter hφ κ s) :=
  (nonlinear_continuous ((speedData φ hφ).density_integrable hκ)
    ((speedData φ hφ).density_nonneg hκ) hs).comp (reflectedX_continuous hφ)

/--
The stated quantitative bound `0≤nonlinearFilter hφ κ s t`.

Use: `chebyshev2.Primal.determinant_difference_core_identity` uses this bound to establish
the precise assertion is `normalizedVelocity φ t*determinantDifferenceDensity hφ hψ κ s
(normalizedX hφ t)= determinantDifferenceCore hφ hψ κ s t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_bounds`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem nonlinearFilter_nonneg {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) (t : ℝ) : 0≤nonlinearFilter hφ κ s t :=
  (nonlinear_bounds ((speedData φ hφ).density_integrable hκ)
    ((speedData φ hφ).density_nonneg hκ) hs _).1
/--
The stated quantitative bound `0≤reflectedNonlinearFilter hφ κ s t`.

Use: `chebyshev2.Primal.determinant_difference_core_identity` uses this bound to establish
the precise assertion is `normalizedVelocity φ t*determinantDifferenceDensity hφ hψ κ s
(normalizedX hφ t)= determinantDifferenceCore hφ hψ κ s t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_bounds`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem reflectedNonlinearFilter_nonneg {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) (t : ℝ) : 0≤reflectedNonlinearFilter hφ κ s t :=
  (nonlinear_bounds ((speedData φ hφ).density_integrable hκ)
    ((speedData φ hφ).density_nonneg hκ) hs _).1

/--
Exact identity `nonlinearFilter hφ κ s 0=0`.

Use: `chebyshev2.Primal.determinant_profile_difference_cubic` rewrites with this identity
to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_left_of_density_zero`,
`chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown in the
proof.
-/
theorem nonlinearFilter_initial {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s : ℝ) :
    nonlinearFilter hφ κ s 0=0 := by
  apply nonlinear_left_of_density_zero
  intro x hx
  apply (speedData φ hφ).density_zero_outside
  simp only [normalizedX,zero_pow (by decide : 3≠0)] at hx
  exact fun hi => (not_lt_of_ge hx) hi.1

/--
Exact identity `nonlinearFilter hφ κ s 1=reflectedNonlinearFilter hφ κ s 1`.

Use: `chebyshev2.Primal.rightNonlinearFilter_parameter_upper` rewrites with this identity
to prove the bound `1+rightNonlinearFilter hφ κ s v≤exp
d*(1+rightNonlinearFilter hψ κ s v)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem nonlinearFilter_join {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s : ℝ) :
    nonlinearFilter hφ κ s 1=reflectedNonlinearFilter hφ κ s 1 := by norm_num [nonlinearFilter,reflectedNonlinearFilter,normalizedX,reflectedX]

/--
The derivative within the stated domain: `HasDerivWithinAt (nonlinearFilter hφ κ s)
(normalizedVelocity φ t*(s*normalizedDensity φ κ t- 2*nonlinearFilter hφ κ s t-(nonlinearFilter
hφ κ s t)^2)) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Primal.shifted_nonlinear_ode` uses this derivative formula to establish
the derivative within the stated domain: `HasDerivWithinAt (fun t => 1+nonlinearFilter hφ κ s
t) (3*(s/κ)*t^2+(1+(s/κ)*t^3*(2-t^3))*normalizedVelocity φ t- normalizedVelocity φ
t*(1+nonlinearFilter hφ κ s t)^2) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_hasDerivAt`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem nonlinearFilter_ode {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (nonlinearFilter hφ κ s)
      (normalizedVelocity φ t*(s*normalizedDensity φ κ t-
        2*nonlinearFilter hφ κ s t-(nonlinearFilter hφ κ s t)^2)) (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_hasDerivAt`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  have h := (nonlinear_hasDerivAt ((speedData φ hφ).density_integrable hκ)
    ((speedData φ hφ).density_nonneg hκ) (density_continuous hφ κ) hs (normalizedX hφ t)).comp_hasDerivWithinAt (h := normalizedX hφ) t (normalizedX_derivative hφ t ht)
  rw [normalized_density hφ κ ht] at h
  convert! h using 1
  dsimp only [normalizedDensity,nonlinearFilter]
  ring

/--
The derivative within the stated domain: `HasDerivWithinAt (reflectedNonlinearFilter hφ κ s)
(-normalizedVelocity φ t*(s*normalizedDensity φ κ t- 2*reflectedNonlinearFilter hφ κ s
t-(reflectedNonlinearFilter hφ κ s t)^2)) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Primal.right_shifted_nonlinear_ode` uses this derivative formula to
establish the derivative formula stated in that declaration.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_hasDerivAt`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem reflectedNonlinearFilter_ode {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (reflectedNonlinearFilter hφ κ s)
      (-normalizedVelocity φ t*(s*normalizedDensity φ κ t-
        2*reflectedNonlinearFilter hφ κ s t-(reflectedNonlinearFilter hφ κ s t)^2))
        (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_hasDerivAt`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  have h := (nonlinear_hasDerivAt ((speedData φ hφ).density_integrable hκ)
    ((speedData φ hφ).density_nonneg hκ) (density_continuous hφ κ) hs (reflectedX hφ t)).comp_hasDerivWithinAt (h := reflectedX hφ) t (reflectedX_derivative hφ t ht)
  rw [reflected_density hφ κ ht] at h
  convert! h using 1
  dsimp only [normalizedDensity,reflectedNonlinearFilter]
  ring

/--
Continuity of the displayed function: `Continuous (linearFilter hφ κ)`.

Use: `chebyshev2.Primal.familyLinearFilter_joint_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (familyLinearFilter hψ hθ κ
reflected).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.Primal.normalizedX_continuous` with the arguments shown in the proof.
-/
theorem linearFilter_continuous {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ : ℝ} (hκ : 0<κ) : Continuous (linearFilter hφ κ) :=
  ((causal_continuous (by norm_num : (0:ℝ)≤2)
    ((speedData φ hφ).density_integrable hκ)).comp (normalizedX_continuous hφ)).const_mul κ
/--
Continuity of the displayed function: `Continuous (reflectedLinearFilter hφ κ)`.

Use: `chebyshev2.Primal.familyLinearFilter_joint_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (familyLinearFilter hψ hθ κ
reflected).uncurry`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.Primal.reflectedX_continuous` with the arguments shown in the proof.
-/
theorem reflectedLinearFilter_continuous {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ : ℝ} (hκ : 0<κ) : Continuous (reflectedLinearFilter hφ κ) :=
  ((causal_continuous (by norm_num : (0:ℝ)≤2)
    ((speedData φ hφ).density_integrable hκ)).comp (reflectedX_continuous hφ)).const_mul κ

/--
The stated quantitative bound `0≤linearFilter hφ κ t`.

Use: `chebyshev2.Primal.familyLinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyLinearFilter hψ hθ κ reflected a t-familyLinearFilter hψ
hθ κ reflected b t|≤ 2*(exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_nonneg`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem linearFilter_nonneg {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ : ℝ} (hκ : 0<κ) (t : ℝ) : 0≤linearFilter hφ κ t :=
  mul_nonneg hκ.le (causal_nonneg (Filter.Eventually.of_forall ((speedData φ hφ).density_nonneg hκ)) _)
/--
The stated quantitative bound `0≤reflectedLinearFilter hφ κ t`.

Use: `chebyshev2.Primal.familyLinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyLinearFilter hψ hθ κ reflected a t-familyLinearFilter hψ
hθ κ reflected b t|≤ 2*(exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_nonneg`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem reflectedLinearFilter_nonneg {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ : ℝ} (hκ : 0<κ) (t : ℝ) : 0≤reflectedLinearFilter hφ κ t :=
  mul_nonneg hκ.le (causal_nonneg (Filter.Eventually.of_forall ((speedData φ hφ).density_nonneg hκ)) _)

/--
Exact identity `linearFilter hφ κ 0=0`.

Use: `chebyshev2.Primal.linearFilter_lower` rewrites with this identity to establish the
stated quantitative bound `t^3*(2-t^3)/2≤linearFilter hφ κ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem linearFilter_initial {φ : ℝ → ℝ} (hφ : Continuous φ) (κ : ℝ) :
    linearFilter hφ κ 0=0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  unfold linearFilter causal normalizedX
  simp only [zero_pow (by decide : 3≠0)]
  have he : (fun x => exp (2*x)*(speedData φ hφ).density κ x)=ᵐ[
      volume.restrict (Iic ((speedData φ hφ).X 0))] (fun _ => (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [(speedData φ hφ).density_zero_outside κ (fun hi => (not_lt_of_ge hx) hi.1),mul_zero]
  rw [integral_congr_ae he,integral_zero,mul_zero,mul_zero]

/--
Exact identity `linearFilter hφ κ 1=reflectedLinearFilter hφ κ 1`.

Use: `chebyshev2.Primal.reflectedLinearFilter_lower` rewrites with this identity to
establish the stated quantitative bound `t^3*(2-t^3)/2≤reflectedLinearFilter hφ κ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem linearFilter_join {φ : ℝ → ℝ} (hφ : Continuous φ) (κ : ℝ) :
    linearFilter hφ κ 1=reflectedLinearFilter hφ κ 1 := by norm_num [linearFilter,reflectedLinearFilter,normalizedX,reflectedX]

/--
The derivative within the stated domain: `HasDerivWithinAt (linearFilter hφ κ)
(normalizedVelocity φ t*(κ*normalizedDensity φ κ t-2*linearFilter hφ κ t)) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Primal.linearFilter_regular_ode` uses this derivative formula to establish
the derivative within the stated domain: `HasDerivWithinAt (linearFilter hφ κ)
(3*t^2+normalizedVelocity φ t*(t^3*(2-t^3)-2*linearFilter hφ κ t)) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_hasDerivAt`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.Primal.density_continuous` with the arguments shown in the proof.
-/
theorem linearFilter_ode {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ : ℝ} (hκ : 0<κ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (linearFilter hφ κ)
      (normalizedVelocity φ t*(κ*normalizedDensity φ κ t-2*linearFilter hφ κ t))
      (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `chebyshev2.Filters.causal_hasDerivAt`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.Primal.density_continuous` with the arguments shown in the proof.
  have h := ((causal_hasDerivAt ((speedData φ hφ).density_integrable hκ)
    (density_continuous hφ κ) (by norm_num : (0:ℝ)≤2) (normalizedX hφ t)).const_mul κ).comp_hasDerivWithinAt (h := normalizedX hφ) t (normalizedX_derivative hφ t ht)
  rw [normalized_density hφ κ ht] at h
  convert! h using 1
  dsimp only [normalizedDensity,linearFilter]
  ring

/--
The derivative within the stated domain: `HasDerivWithinAt (reflectedLinearFilter hφ κ)
(-normalizedVelocity φ t*(κ*normalizedDensity φ κ t-2*reflectedLinearFilter hφ κ t)) (Icc (0:ℝ)
1) t`.

Use: `chebyshev2.Primal.rightLinearFilter_regular_ode` uses this derivative formula to
establish the derivative within the stated domain: `HasDerivWithinAt (rightLinearFilter hφ κ)
(3*(2-v)^2+normalizedVelocity φ (2-v)* ((2-v)^3*(2-(2-v)^3)-2*rightLinearFilter hφ κ v)) (Icc
(1:ℝ) 2) v`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_hasDerivAt`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.Primal.density_continuous` with the arguments shown in the proof.
-/
theorem reflectedLinearFilter_ode {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ : ℝ} (hκ : 0<κ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (reflectedLinearFilter hφ κ)
      (-normalizedVelocity φ t*(κ*normalizedDensity φ κ t-2*reflectedLinearFilter hφ κ t))
      (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `chebyshev2.Filters.causal_hasDerivAt`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.Primal.density_continuous` with the arguments shown in the proof.
  have h := ((causal_hasDerivAt ((speedData φ hφ).density_integrable hκ)
    (density_continuous hφ κ) (by norm_num : (0:ℝ)≤2) (reflectedX hφ t)).const_mul κ).comp_hasDerivWithinAt (h := reflectedX hφ) t (reflectedX_derivative hφ t ht)
  rw [reflected_density hφ κ ht] at h
  convert! h using 1
  dsimp only [normalizedDensity,reflectedLinearFilter]
  ring

end
end chebyshev2.Primal
