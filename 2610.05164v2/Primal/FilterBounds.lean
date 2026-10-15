import «2610.05164v2».Primal.Filters

/-!
Article: 2610.05164v2, Proposition 13.
Intrinsic ground-coordinate bounds for every actual primal filter.
Use: `«2610.05164v2».Primal.reflectedLinearFilter_bound` feeds
`«2610.05164v2».Primal.reflectedLinearFilter_parameter_bound` (reflected Linear Filter parameter
bound).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set «2610.05164v2».PrescribedSpeed «2610.05164v2».Filters «2610.05164v2».GroundState
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `groundWitness` of type `GroundWitness ((speedData φ hφ).density_integrable hκ)
((speedData φ hφ).density_nonneg hκ)` by `Classical.choice (ground_state ((speedData φ
hφ).density_integrable hκ) ((speedData φ hφ).density_nonneg hκ) ((speedData φ
hφ).density_nonzero hκ))`.

Use: `«2610.05164v2».Primal.linearFilter_bound` rewrites with this definition to establish the
stated quantitative bound `linearFilter hφ κ t≤t^3`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def groundWitness {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ) :
    GroundWitness ((speedData φ hφ).density_integrable hκ) ((speedData φ hφ).density_nonneg hκ) :=
  Classical.choice (ground_state ((speedData φ hφ).density_integrable hκ)
    ((speedData φ hφ).density_nonneg hκ) ((speedData φ hφ).density_nonzero hκ))

/--
The stated quantitative bound `nonlinearFilter hφ κ s t≤(s/κ)*t^3`.

Use: `«2610.05164v2».Primal.familyNonlinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyNonlinearFilter hψ hθ κ s reflected a
t-familyNonlinearFilter hψ hθ κ s reflected b t|≤ (exp (‖a-b‖*∑ i,‖unitDirection (hθ
i)‖)-1)*(1+2*s/κ)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_le_coordinate`,
`«2610.05164v2».PrescribedSpeed.SpeedData.q_X`,
`«2610.05164v2».PrescribedSpeed.SpeedData.ground_coordinate` with the arguments shown in the
proof.
-/
theorem nonlinearFilter_bound {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s t : ℝ} (hκ : 0<κ) (hs : 0≤s) (ht : t∈Icc (0:ℝ) 1) :
    nonlinearFilter hφ κ s t≤(s/κ)*t^3 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_le_coordinate`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.q_X`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.ground_coordinate` with the arguments shown in
  -- the proof.
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  have h := nonlinear_le_coordinate (groundWitness hφ hκ) hs (normalizedX hφ t)
  rw [(speedData φ hφ).groundParameter_density hκ,
    (speedData φ hφ).ground_coordinate hκ (groundWitness hφ hκ)] at h
  rw [normalizedX,(speedData φ hφ).q_X ⟨pow_nonneg ht.1 _,by linarith⟩] at h
  exact h

/--
The stated quantitative bound `reflectedNonlinearFilter hφ κ s t≤(s/κ)*(2-t^3)`.

Use: `«2610.05164v2».Primal.familyNonlinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyNonlinearFilter hψ hθ κ s reflected a
t-familyNonlinearFilter hψ hθ κ s reflected b t|≤ (exp (‖a-b‖*∑ i,‖unitDirection (hθ
i)‖)-1)*(1+2*s/κ)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_le_coordinate`,
`«2610.05164v2».PrescribedSpeed.SpeedData.q_X`,
`«2610.05164v2».PrescribedSpeed.SpeedData.ground_coordinate` with the arguments shown in the
proof.
-/
theorem reflectedNonlinearFilter_bound {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s t : ℝ} (hκ : 0<κ) (hs : 0≤s) (ht : t∈Icc (0:ℝ) 1) :
    reflectedNonlinearFilter hφ κ s t≤(s/κ)*(2-t^3) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_le_coordinate`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.q_X`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.ground_coordinate` with the arguments shown in
  -- the proof.
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  have h := nonlinear_le_coordinate (groundWitness hφ hκ) hs (reflectedX hφ t)
  rw [(speedData φ hφ).groundParameter_density hκ,
    (speedData φ hφ).ground_coordinate hκ (groundWitness hφ hκ)] at h
  rw [reflectedX,(speedData φ hφ).q_X ⟨by linarith,by linarith [pow_nonneg ht.1 3]⟩] at h
  exact h

/--
The stated quantitative bound `linearFilter hφ κ t≤t^3`.

Use: `«2610.05164v2».Primal.linearFilter_parameter_bound` uses this bound to establish the
stated quantitative bound `|linearFilter hφ κ t-linearFilter hψ κ t|≤(exp d-1)*linearDefect hψ
κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.linear_le_coordinate`,
`«2610.05164v2».PrescribedSpeed.SpeedData.q_X`,
`«2610.05164v2».PrescribedSpeed.SpeedData.ground_coordinate` with the arguments shown in the
proof.
-/
theorem linearFilter_bound {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) : linearFilter hφ κ t≤t^3 := by
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  have h := linear_le_coordinate (groundWitness hφ hκ) (normalizedX hφ t)
  rw [«2610.05164v2».Filters.linear,(speedData φ hφ).groundParameter_density hκ,
    (speedData φ hφ).ground_coordinate hκ (groundWitness hφ hκ)] at h
  rw [normalizedX,(speedData φ hφ).q_X ⟨pow_nonneg ht.1 _,by linarith⟩] at h
  exact h

/--
The stated quantitative bound `reflectedLinearFilter hφ κ t≤2-t^3`.

Use: `«2610.05164v2».Primal.reflectedLinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|reflectedLinearFilter hφ κ t-reflectedLinearFilter hψ κ t|≤
(exp d-1)*(2-t^3-reflectedLinearFilter hψ κ t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.linear_le_coordinate`,
`«2610.05164v2».PrescribedSpeed.SpeedData.q_X`,
`«2610.05164v2».PrescribedSpeed.SpeedData.ground_coordinate` with the arguments shown in the
proof.
-/
theorem reflectedLinearFilter_bound {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) : reflectedLinearFilter hφ κ t≤2-t^3 := by
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  have h := linear_le_coordinate (groundWitness hφ hκ) (reflectedX hφ t)
  rw [«2610.05164v2».Filters.linear,(speedData φ hφ).groundParameter_density hκ,
    (speedData φ hφ).ground_coordinate hκ (groundWitness hφ hκ)] at h
  rw [reflectedX,(speedData φ hφ).q_X ⟨by linarith,by linarith [pow_nonneg ht.1 3]⟩] at h
  exact h

end
end «2610.05164v2».Primal
