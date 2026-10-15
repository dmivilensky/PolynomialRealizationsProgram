import «2606.16671v2».SineJacobi.ProfileODE
import «2606.16671v2».Analysis.PositiveConcavity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: 2606.16671v2, Theorem 5.2.
Profile Higher Derivatives.
Use: `«2606.16671v2».SineJacobi.sineProfile_contDiffOn` feeds
`«2606.16671v2».SineJacobi.energyDensity_weighted_derivatives` (Explicit fourth-order control for
the actual squared density).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set Filter Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/--
Defines `profilePotential` of type `ℝ` by `Real.pi^2/(4*sin (Real.pi*t)^2)`.

Use: `«2606.16671v2».SineJacobi.sineProfile_contDiffOn` uses this definition to establish
smoothness to the stated order: `ContDiffOn ℝ n sineProfile (Ioo (0:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def profilePotential (t : ℝ) : ℝ := Real.pi^2/(4*sin (Real.pi*t)^2)
/--
Defines `profilePotential₁` of type `ℝ` by `-Real.pi^3*cos (Real.pi*t)/(2*sin (Real.pi*t)^3)`.

Use: `«2606.16671v2».SineJacobi.profilePotential_deriv` rewrites with this definition to
establish the actual derivative at the stated point: `HasDerivAt profilePotential
(profilePotential₁ t) t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def profilePotential₁ (t : ℝ) : ℝ := -Real.pi^3*cos (Real.pi*t)/(2*sin (Real.pi*t)^3)
/--
Defines `profilePotential₂` of type `ℝ` by `Real.pi^4*(1+2*cos (Real.pi*t)^2)/(2*sin
(Real.pi*t)^4)`.

Use: `«2606.16671v2».SineJacobi.profilePotential₁_deriv` rewrites with this definition to
establish the actual derivative at the stated point: `HasDerivAt profilePotential₁
(profilePotential₂ t) t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def profilePotential₂ (t : ℝ) : ℝ :=
  Real.pi^4*(1+2*cos (Real.pi*t)^2)/(2*sin (Real.pi*t)^4)
/--
Defines `sineProfile₃` of type `ℝ` by `-profilePotential₁ t*sineProfile t-profilePotential
t*sineProfile₁ t`.

Use: `«2606.16671v2».SineJacobi.sineProfile₂_deriv` rewrites with this definition to establish
the actual derivative at the stated point: `HasDerivAt sineProfile₂ (sineProfile₃ t) t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def sineProfile₃ (t : ℝ) : ℝ :=
  -profilePotential₁ t*sineProfile t-profilePotential t*sineProfile₁ t
/--
Defines `sineProfile₄` of type `ℝ` by `-profilePotential₂ t*sineProfile t-2*profilePotential₁
t*sineProfile₁ t- profilePotential t*sineProfile₂ t`.

Use: `«2606.16671v2».SineJacobi.sineProfile₃_deriv` rewrites with this definition to establish
the actual derivative at the stated point: `HasDerivAt sineProfile₃ (sineProfile₄ t) t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def sineProfile₄ (t : ℝ) : ℝ :=
  -profilePotential₂ t*sineProfile t-2*profilePotential₁ t*sineProfile₁ t-
    profilePotential t*sineProfile₂ t

/--
The actual derivative at the stated point: `HasDerivAt profilePotential (profilePotential₁ t)
t`.

Use: `«2606.16671v2».SineJacobi.sineProfile₂_deriv` uses this derivative formula to establish
the actual derivative at the stated point: `HasDerivAt sineProfile₂ (sineProfile₃ t) t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem profilePotential_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt profilePotential (profilePotential₁ t) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs : sin (Real.pi*t) ≠ 0 := (sin_pos_of_mem_Ioo
    ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩).ne'
  have hd := (hasDerivAt_const t (Real.pi^2)).div
    ((((hasDerivAt_id t).const_mul Real.pi).sin.pow 2).const_mul 4) (by positivity : 4*sin (Real.pi*t)^2 ≠ 0)
  convert hd using 1
  · rfl
  · simp only [profilePotential₁, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    generalize sin (Real.pi*t) = s at hs ⊢
    generalize cos (Real.pi*t) = c
    field_simp [hs]
    ring

/--
The actual derivative at the stated point: `HasDerivAt profilePotential₁ (profilePotential₂ t)
t`.

Use: `«2606.16671v2».SineJacobi.sineProfile₃_deriv` uses this derivative formula to establish
the actual derivative at the stated point: `HasDerivAt sineProfile₃ (sineProfile₄ t) t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem profilePotential₁_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt profilePotential₁ (profilePotential₂ t) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs : sin (Real.pi*t) ≠ 0 := (sin_pos_of_mem_Ioo
    ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩).ne'
  have hd := ((((hasDerivAt_id t).const_mul Real.pi).cos).const_mul (-Real.pi^3)).div
    ((((hasDerivAt_id t).const_mul Real.pi).sin.pow 3).const_mul 2) (by positivity : 2*sin (Real.pi*t)^3 ≠ 0)
  convert hd using 1
  · funext u; simp only [profilePotential₁, Pi.div_apply, Pi.pow_apply, id_eq]
  · simp only [profilePotential₂, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub]
    have hsc := sin_sq_add_cos_sq (Real.pi*t)
    generalize sin (Real.pi*t) = s at hs hsc ⊢
    generalize cos (Real.pi*t) = c at hsc ⊢
    field_simp [hs]
    nlinarith [hsc]

/--
Exact identity `sineProfile₂ t = -profilePotential t*sineProfile t`.

Use: `«2606.16671v2».SineJacobi.sineProfile_contDiffOn` rewrites with this identity to
establish smoothness to the stated order: `ContDiffOn ℝ n sineProfile (Ioo (0:ℝ) 1)`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineProfile_explicit_ode` with
the arguments shown in the proof.
-/
theorem sineProfile₂_eq {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    sineProfile₂ t = -profilePotential t*sineProfile t := by
  have h := sineProfile_explicit_ode ht
  change sineProfile₂ t+profilePotential t*sineProfile t = 0 at h
  linarith

/--
The actual derivative at the stated point: `HasDerivAt sineProfile₂ (sineProfile₃ t) t`.

Use: `«2606.16671v2».SineJacobi.profileDerivative_eq` uses this derivative formula to establish
exact identity `iteratedDeriv n sineProfile t = profileDerivative n t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineProfile₂_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt sineProfile₂ (sineProfile₃ t) t := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hd := ((profilePotential_deriv ht).mul (sineProfile_deriv ht)).neg
  have he : sineProfile₂ =ᶠ[𝓝 t] -(profilePotential*sineProfile) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    simpa only [Pi.neg_apply, Pi.mul_apply, neg_mul] using sineProfile₂_eq hu
  convert hd.congr_of_eventuallyEq he using 1
  simp only [sineProfile₃]
  ring

/--
The actual derivative at the stated point: `HasDerivAt sineProfile₃ (sineProfile₄ t) t`.

Use: `«2606.16671v2».SineJacobi.profileDerivative_eq` uses this derivative formula to establish
exact identity `iteratedDeriv n sineProfile t = profileDerivative n t`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.profilePotential₁_deriv`,
`«2606.16671v2».SineJacobi.sineProfile_deriv`,
`«2606.16671v2».SineJacobi.profilePotential_deriv` with the arguments shown in the proof.
-/
theorem sineProfile₃_deriv {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt sineProfile₃ (sineProfile₄ t) t := by
  have hd := (((profilePotential₁_deriv ht).neg.mul (sineProfile_deriv ht)).sub
    ((profilePotential_deriv ht).mul (sineProfile₁_deriv ht)))
  convert hd using 1
  · rfl
  · simp only [sineProfile₄, Pi.neg_apply]; ring

/--
The stated quantitative bound `-sineProfile t/(1-t) ≤ sineProfile₁ t ∧ sineProfile₁ t ≤
sineProfile t/t`.

Use: `«2606.16671v2».SineJacobi.sineProfile_weighted_derivatives` uses this bound to establish
the stated quantitative bound `WeightedDerivatives sineProfile x r (fun n =>
profileDerivativeBound n*sineProfile x) 4`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.positive_concave_slope`,
`«2606.16671v2».SineJacobi.sineProfile_deriv`, `«2606.16671v2».SineJacobi.sineProfile₁_deriv`
with the arguments shown in the proof.
-/
theorem sineProfile_slope_bounds {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    -sineProfile t/(1-t) ≤ sineProfile₁ t ∧ sineProfile₁ t ≤ sineProfile t/t := by
  -- Use the identities/estimates `«2606.16671v2».Analysis.positive_concave_slope`,
  -- `«2606.16671v2».SineJacobi.sineProfile_deriv`,
  -- `«2606.16671v2».SineJacobi.sineProfile₁_deriv` with the arguments shown in the proof.
  apply «2606.16671v2».Analysis.positive_concave_slope
    (fun _ hu => sineProfile_deriv hu) (fun _ hu => sineProfile₁_deriv hu)
    (fun _ hu => sineProfile_pos hu) _ ht
  intro u hu
  rw [sineProfile₂_eq hu]
  simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg
    (show 0 ≤ profilePotential u by unfold profilePotential; positivity) (sineProfile_pos hu).le)

/--
Smoothness to the stated order: `ContDiffOn ℝ n sineProfile (Ioo (0:ℝ) 1)`.

Use: `«2606.16671v2».SineJacobi.energyDensity_weighted_derivatives` uses this assertion to
establish the stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Induct on `m`; the recursive step uses the previous-stage assertion.
-/
theorem sineProfile_contDiffOn (n : ℕ) : ContDiffOn ℝ n sineProfile (Ioo (0:ℝ) 1) := by
  -- Induct on `m`; the recursive step uses the previous-stage assertion.
  have hq (m : ℕ) : ContDiffOn ℝ m profilePotential (Ioo (0:ℝ) 1) := by
    unfold profilePotential
    apply ContDiffOn.div contDiffOn_const (by fun_prop)
    intro t ht
    have hs : sin (Real.pi*t) ≠ 0 := (sin_pos_of_mem_Ioo
      ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩).ne'
    positivity
  have hall (m : ℕ) : ContDiffOn ℝ m sineProfile (Ioo (0:ℝ) 1) ∧
      ContDiffOn ℝ m sineProfile₁ (Ioo (0:ℝ) 1) := by
    induction m with
    | zero =>
      exact ⟨contDiffOn_zero.mpr (fun _ ht => (sineProfile_deriv ht).continuousAt.continuousWithinAt),
        contDiffOn_zero.mpr (fun _ ht => (sineProfile₁_deriv ht).continuousAt.continuousWithinAt)⟩
    | succ m ih =>
      have hder : EqOn (deriv sineProfile) sineProfile₁ (Ioo (0:ℝ) 1) :=
        fun _ ht => (sineProfile_deriv ht).deriv
      have hder₁ : EqOn (deriv sineProfile₁) (fun t => -profilePotential t*sineProfile t)
          (Ioo (0:ℝ) 1) := fun _ ht => by
        rw [(sineProfile₁_deriv ht).deriv, sineProfile₂_eq ht]
      constructor
      · rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
        refine ⟨fun _ ht => (sineProfile_deriv ht).differentiableAt.differentiableWithinAt,
          by simp, ?_⟩
        exact ih.2.congr hder
      · rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
        refine ⟨fun _ ht => (sineProfile₁_deriv ht).differentiableAt.differentiableWithinAt,
          by simp, ?_⟩
        exact ((hq m).neg.mul ih.1).congr hder₁
  exact (hall n).1

end
end «2606.16671v2».SineJacobi
