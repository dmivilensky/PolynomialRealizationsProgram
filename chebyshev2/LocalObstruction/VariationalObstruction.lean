import chebyshev2.LocalObstruction.CurveBasis
import chebyshev2.LocalObstruction.NonstationaryTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Article: chebyshev2, Theorem 6.1.
The final variational argument of H.
Use: `chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient_with_property` feeds
`chebyshev2.LocalObstruction.finite_observation_no_local_bound_with_property` (finite
observation no local bound with property).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory chebyshev2.SineContinuum Asymptotics
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `densityEnergy` of type `ℝ` by `∫ x, f x*sqrt (f x)`.

Use: `chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient` uses this definition to
establish constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f
x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f
x))=1 ∧ (∀ x, |f x-m x|<ε) ∧ densityEnergy f<B f`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def densityEnergy (f : ℝ → ℝ) : ℝ := ∫ x, f x*sqrt (f x)

/--
Constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f x-m x) ∧
HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f x))=1 ∧ (∀
x, |f x-m x|<ε) ∧ densityEnergy f<B f`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities. Intersect the eventual or almost-everywhere hypotheses, then prove
the asserted relation at an arbitrary point in that intersection.
-/
theorem no_local_lower_bound_of_gradient {B : (ℝ → ℝ) → ℝ} {g : ℝ → ℝ}
    (hg : Continuous g) {c₀ c₁ : ℝ}
    (htail : (fun x => g x-c₀-c₁*exp (-2*x)) =o[atTop] n)
    (heq : B m=densityEnergy m)
    (hderiv : ∀ v w : SmoothTest, 0<(∫ x, n x*w x) →
      HasDerivAt (fun t => B (curveDensity (amplitudeDirection v) w t)) (∫ x, v x*g x) 0)
    {ε : ℝ} (hε : 0<ε) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ ∞ (fun x => f x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧
      (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f x))=1 ∧
      (∀ x, |f x-m x|<ε) ∧ densityEnergy f<B f := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  obtain ⟨v,hv,hv₁,hvne⟩ := sine_nonstationary_test hg htail
  obtain ⟨w,hw₀,hw⟩ := amplitude_correction_direction
  let f := curveDensity (amplitudeDirection v) w
  have hE := tangent_energy_derivative v w hw
  have hB := hderiv v w hw
  have hΔ : HasDerivAt (fun t => densityEnergy (f t)-B (f t))
      (∫ x, v x*((3/2:ℝ)*n x-g x)) 0 := by
    have hi := integral_sub (test_integrable v (g := fun x => (3/2:ℝ)*n x) (continuous_const.mul n_continuous))
      (test_integrable v hg)
    have he : (∫ x, v x*((3/2:ℝ)*n x-g x))=
        (∫ x, v x*((3/2:ℝ)*n x))-(∫ x, v x*g x) := by
      simp only [mul_sub]
      exact hi
    rw [he]
    exact hE.sub hB
  by_contra h
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), 0≤densityEnergy (f t)-B (f t) := by
    filter_upwards [curveDensity_mass (amplitudeDirection v) w (amplitudeDirection_tangent v hv) hw,
      curveDensity_sqrt_mass (amplitudeDirection v) w hv₁ hw₀ hw,
      curveDensity_uniform_small (amplitudeDirection v) w hw hε] with t hM hR hsmall
    have hle : B (f t)≤densityEnergy (f t) := by
      by_contra ht
      apply h
      exact ⟨f t,(curveDensity_increment (amplitudeDirection v) w t).1,
        (curveDensity_increment (amplitudeDirection v) w t).2,
        fun x => sq_nonneg _,hM,hR,hsmall,lt_of_not_ge ht⟩
    exact sub_nonneg.mpr hle
  have hz : densityEnergy (f 0)-B (f 0)=0 := by
    simp only [f,curveDensity_zero,heq,sub_self]
  have hmin : IsLocalMin (fun t => densityEnergy (f t)-B (f t)) 0 := by
    filter_upwards [hnear] with t ht
    simpa only [hz] using ht
  exact hvne (hmin.hasDerivAt_eq_zero hΔ)


/--
Constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f x-m x) ∧
HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f x))=1 ∧ (∀
x, |f x-m x|<ε) ∧ P f ∧ densityEnergy f<B f`.

Use: `chebyshev2.LocalObstruction.finite_observation_no_local_bound_with_property` uses
this identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities. Intersect the eventual or almost-everywhere hypotheses, then prove
the asserted relation at an arbitrary point in that intersection.
-/
theorem no_local_lower_bound_of_gradient_with_property {B : (ℝ → ℝ) → ℝ} {g : ℝ → ℝ}
    (hg : Continuous g) {c₀ c₁ : ℝ}
    (htail : (fun x => g x-c₀-c₁*exp (-2*x)) =o[atTop] n)
    (heq : B m=densityEnergy m)
    (hderiv : ∀ v w : SmoothTest, 0<(∫ x, n x*w x) →
      HasDerivAt (fun t => B (curveDensity (amplitudeDirection v) w t)) (∫ x, v x*g x) 0)
    (P : (ℝ → ℝ) → Prop)
    (hP : ∀ v w : SmoothTest, 0<(∫ x,n x*w x) →
      ∀ᶠ t in 𝓝 (0:ℝ),P (curveDensity (amplitudeDirection v) w t))
    {ε : ℝ} (hε : 0<ε) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ ∞ (fun x => f x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧
      (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f x))=1 ∧
      (∀ x, |f x-m x|<ε) ∧ P f ∧ densityEnergy f<B f := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  obtain ⟨v,hv,hv₁,hvne⟩ := sine_nonstationary_test hg htail
  obtain ⟨w,hw₀,hw⟩ := amplitude_correction_direction
  let f := curveDensity (amplitudeDirection v) w
  have hE := tangent_energy_derivative v w hw
  have hB := hderiv v w hw
  have hΔ : HasDerivAt (fun t => densityEnergy (f t)-B (f t))
      (∫ x, v x*((3/2:ℝ)*n x-g x)) 0 := by
    have hi := integral_sub (test_integrable v (g := fun x => (3/2:ℝ)*n x) (continuous_const.mul n_continuous))
      (test_integrable v hg)
    have he : (∫ x, v x*((3/2:ℝ)*n x-g x))=
        (∫ x, v x*((3/2:ℝ)*n x))-(∫ x, v x*g x) := by
      simp only [mul_sub]
      exact hi
    rw [he]
    exact hE.sub hB
  by_contra h
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), 0≤densityEnergy (f t)-B (f t) := by
    filter_upwards [curveDensity_mass (amplitudeDirection v) w (amplitudeDirection_tangent v hv) hw,
      curveDensity_sqrt_mass (amplitudeDirection v) w hv₁ hw₀ hw,
      curveDensity_uniform_small (amplitudeDirection v) w hw hε,hP v w hw] with t hM hR hsmall hp
    have hle : B (f t)≤densityEnergy (f t) := by
      by_contra ht
      apply h
      exact ⟨f t,(curveDensity_increment (amplitudeDirection v) w t).1,
        (curveDensity_increment (amplitudeDirection v) w t).2,
        fun x => sq_nonneg _,hM,hR,hsmall,hp,lt_of_not_ge ht⟩
    exact sub_nonneg.mpr hle
  have hz : densityEnergy (f 0)-B (f 0)=0 := by
    simp only [f,curveDensity_zero,heq,sub_self]
  have hmin : IsLocalMin (fun t => densityEnergy (f t)-B (f t)) 0 := by
    filter_upwards [hnear] with t ht
    simpa only [hz] using ht
  exact hvne (hmin.hasDerivAt_eq_zero hΔ)

end
end chebyshev2.LocalObstruction
