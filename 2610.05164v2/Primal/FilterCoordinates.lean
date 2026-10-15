import «2610.05164v2».Primal.Density
import «2610.05164v2».Calculus.ClosedInterval
import «2610.05164v2».Filters.ContinuousDensity
import «2610.05164v2».Filters.OutsideSupport

/-!
Article: 2610.05164v2, Proposition 13.
The actual primal density in the regular cubic time coordinate.
Use: `«2610.05164v2».Primal.reflected_density` feeds
`«2610.05164v2».Primal.reflectedLinearFilter_ode` (reflected Linear Filter ode).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set MeasureTheory Real «2610.05164v2».PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `normalizedX` of type `ℝ` by `(speedData φ hφ).X (t^3)`.

Use: `«2610.05164v2».Primal.normalized_density` rewrites with this definition to establish the
precise assertion is `(speedData φ hφ).density κ (normalizedX hφ t)= (t^2*exp (φ
t)+t^3*(2-t^3))/κ`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.
-/
def normalizedX {φ : ℝ → ℝ} (hφ : Continuous φ) (t : ℝ) : ℝ :=
  (speedData φ hφ).X (t^3)
/--
Defines `reflectedX` of type `ℝ` by `(speedData φ hφ).X (2-t^3)`.

Use: `«2610.05164v2».Primal.reflected_density` rewrites with this definition to establish the
precise assertion is `(speedData φ hφ).density κ (reflectedX hφ t)= (t^2*exp (φ
t)+t^3*(2-t^3))/κ`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def reflectedX {φ : ℝ → ℝ} (hφ : Continuous φ) (t : ℝ) : ℝ :=
  (speedData φ hφ).X (2-t^3)
/--
Defines `normalizedVelocity` of type `ℝ` by `3*exp (-φ t)`.

Use: `«2610.05164v2».Primal.reflectedX_derivative` rewrites with this definition to establish
establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (reflectedX hφ)
(-normalizedVelocity φ t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.
-/
def normalizedVelocity (φ : ℝ → ℝ) (t : ℝ) : ℝ := 3*exp (-φ t)

/--
The actual derivative at the stated point: `HasDerivAt (speedData φ hφ).X (speed φ q)⁻¹ q`.

Use: `«2610.05164v2».Primal.normalizedX_derivative` uses this derivative formula to establish
establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (normalizedX
hφ) (normalizedVelocity φ t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem X_derivative {φ : ℝ → ℝ} (hφ : Continuous φ) {q : ℝ}
    (hq : q∈Ioo (0:ℝ) 2) :
    HasDerivAt (speedData φ hφ).X (speed φ q)⁻¹ q := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  let S := speedData φ hφ
  -- Establish continuity hcD before using the function at limits or in calculus arguments.
  have hcD : ContinuousAt S.D q := (speed_continuous hφ).continuousAt
  -- Establish continuity hcr before using the function at limits or in calculus arguments.
  have hcr : ContinuousAt S.reciprocal q := by
    apply (hcD.inv₀ (S.positive q hq).ne').congr
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
    exact (indicator_of_mem ht (fun q => (S.D q)⁻¹)).symm
  have hm : Measurable S.reciprocal := S.measurable.inv.indicator measurableSet_Ioo
  have h := intervalIntegral.integral_hasDerivAt_right (a := 1) (b := q)
    S.reciprocal_integrable_global.intervalIntegrable
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hcr
  change HasDerivAt S.X (S.reciprocal q) q at h
  rw [SpeedData.reciprocal,indicator_of_mem hq] at h
  exact h

/--
Continuity of the displayed function: `Continuous (normalizedX hφ)`.

Use: `«2610.05164v2».Primal.normalizedX_derivative` uses this continuity result to establish
establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (normalizedX
hφ) (normalizedVelocity φ t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.X_continuous`
with the arguments shown in the proof.
-/
theorem normalizedX_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous (normalizedX hφ) :=
  (speedData φ hφ).X_continuous.comp (continuous_id.pow 3)
/--
Continuity of the displayed function: `Continuous (reflectedX hφ)`.

Use: `«2610.05164v2».Primal.reflectedX_derivative` uses this continuity result to establish
establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (reflectedX hφ)
(-normalizedVelocity φ t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.X_continuous`
with the arguments shown in the proof.
-/
theorem reflectedX_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous (reflectedX hφ) :=
  (speedData φ hφ).X_continuous.comp (continuous_const.sub (continuous_id.pow 3))
/--
Continuity of the displayed function: `Continuous (normalizedVelocity φ)`.

Use: `«2610.05164v2».Primal.normalizedX_derivative` uses this continuity result to establish
establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (normalizedX
hφ) (normalizedVelocity φ t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem normalizedVelocity_continuous {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous (normalizedVelocity φ) := by
  change Continuous (fun t:ℝ => 3*exp (-φ t))
  fun_prop

/--
Establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (normalizedX
hφ) (normalizedVelocity φ t) (Icc (0:ℝ) 1) t`.

Use: `«2610.05164v2».Primal.half_integral_cubic` uses this assertion to establish the precise
assertion is `(∫ x in Iic (0:ℝ),f x)= ∫ t in (0:ℝ)..1,normalizedVelocity φ t*f (normalizedX hφ
t)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedX_derivative {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (normalizedX hφ)
      (normalizedVelocity φ t) (Icc (0:ℝ) 1) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  apply «2610.05164v2».Calculus.hasDerivWithinAt_Icc_of_continuous_derivative zero_lt_one
    (normalizedX_continuous hφ).continuousOn (normalizedVelocity_continuous hφ).continuousOn
  intro t ht
  have ht3 : t^3<1 := pow_lt_one₀ ht.1.le ht.2 (by decide)
  have hq : t^3∈Ioo (0:ℝ) 2 := ⟨pow_pos ht.1 _,by linarith⟩
  have h := (X_derivative hφ hq).comp (h := fun u:ℝ => u^3) t ((hasDerivAt_id t).pow 3)
  rw [speed_cubic φ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  simp only [normalizedVelocity,exp_neg,id_eq,Nat.cast_ofNat,
    show (3:Nat)-1=2 from rfl,mul_one]
  field_simp [ht.1.ne',exp_ne_zero]

/--
Establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (reflectedX hφ)
(-normalizedVelocity φ t) (Icc (0:ℝ) 1) t`.

Use: `«2610.05164v2».Primal.reflectedLinearFilter_ode` uses this assertion to establish the
derivative within the stated domain: `HasDerivWithinAt (reflectedLinearFilter hφ κ)
(-normalizedVelocity φ t*(κ*normalizedDensity φ κ t-2*reflectedLinearFilter hφ κ t)) (Icc (0:ℝ)
1) t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem reflectedX_derivative {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (reflectedX hφ)
      (-normalizedVelocity φ t) (Icc (0:ℝ) 1) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  apply «2610.05164v2».Calculus.hasDerivWithinAt_Icc_of_continuous_derivative zero_lt_one
    (reflectedX_continuous hφ).continuousOn (normalizedVelocity_continuous hφ).neg.continuousOn
  intro t ht
  have ht3 : t^3<1 := pow_lt_one₀ ht.1.le ht.2 (by decide)
  have hq : 2-t^3∈Ioo (0:ℝ) 2 := ⟨by linarith,by linarith [pow_pos ht.1 3]⟩
  have hD : speed φ (2-t^3)=t^2*exp (φ t) := by
    rw [speed,coordinate_reflection]
    exact speed_cubic φ ⟨ht.1.le,ht.2.le⟩
  have h := (X_derivative hφ hq).comp (h := fun u:ℝ => 2-u^3) t (((hasDerivAt_id t).pow 3).const_sub 2)
  rw [hD] at h
  convert! h using 1
  simp only [normalizedVelocity,Pi.neg_apply,exp_neg,id_eq,Nat.cast_ofNat,
    show (3:Nat)-1=2 from rfl,mul_one]
  field_simp [ht.1.ne',exp_ne_zero]

/--
The precise assertion is `(speedData φ hφ).density κ (normalizedX hφ t)= (t^2*exp (φ
t)+t^3*(2-t^3))/κ`.

Use: `«2610.05164v2».Primal.determinant_difference_core_identity` rewrites with this identity
to establish `normalizedVelocity φ t*determinantDifferenceDensity hφ
hψ κ s (normalizedX hφ t)= determinantDifferenceCore hφ hψ κ s t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.density_formula`,
`«2610.05164v2».PrescribedSpeed.SpeedData.q_X`, `«2610.05164v2».Primal.speed_cubic` with the
arguments shown in the proof.
-/
theorem normalized_density {φ : ℝ → ℝ} (hφ : Continuous φ) (κ : ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (speedData φ hφ).density κ (normalizedX hφ t)=
      (t^2*exp (φ t)+t^3*(2-t^3))/κ := by
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  rw [density_formula hφ,SpeedData.Q,normalizedX,
    (speedData φ hφ).q_X ⟨pow_nonneg ht.1 _,by linarith⟩,speed_cubic φ ht]

/--
The precise assertion is `(speedData φ hφ).density κ (reflectedX hφ t)= (t^2*exp (φ
t)+t^3*(2-t^3))/κ`.

Use: `«2610.05164v2».Primal.reflectedLinearFilter_ode` rewrites with this identity to establish
the derivative within the stated domain: `HasDerivWithinAt (reflectedLinearFilter hφ κ)
(-normalizedVelocity φ t*(κ*normalizedDensity φ κ t-2*reflectedLinearFilter hφ κ t)) (Icc (0:ℝ)
1) t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.density_formula`,
`«2610.05164v2».PrescribedSpeed.SpeedData.q_X`, `«2610.05164v2».Primal.coordinate_reflection`
with the arguments shown in the proof.
-/
theorem reflected_density {φ : ℝ → ℝ} (hφ : Continuous φ) (κ : ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (speedData φ hφ).density κ (reflectedX hφ t)=
      (t^2*exp (φ t)+t^3*(2-t^3))/κ := by
  -- Use the identities/estimates `«2610.05164v2».Primal.density_formula`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.q_X`,
  -- `«2610.05164v2».Primal.coordinate_reflection` with the arguments shown in the proof.
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  rw [density_formula hφ,SpeedData.Q,reflectedX,
    (speedData φ hφ).q_X ⟨by linarith,by linarith [pow_nonneg ht.1 3]⟩]
  have hD : speed φ (2-t^3)=speed φ (t^3) := by rw [speed,speed,coordinate_reflection]
  rw [hD,speed_cubic φ ht]
  congr 1
  ring

end
end «2610.05164v2».Primal
