import chebyshev1.SineJacobi.EllipticODE
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: chebyshev2, Proposition 2.
The first/second elliptic-integral relation is proved by an actual integration-by-parts boundary
term, using chebyshev1's derivative integral.
Use: `chebyshev2.SineContinuum.ellipticE_difference` feeds
`chebyshev2.SineContinuum.ellipticLegendre_boundary` (elliptic Legendre boundary).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open chebyshev1.SineJacobi Set Real MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The complete second elliptic integral, in the modulus convention of chebyshev1.

Use: `chebyshev2.SineContinuum.ellipticE_continuous` rewrites with this definition to
establish continuity of the displayed function: `Continuous ellipticE`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.
-/
def ellipticE (k : ℝ) : ℝ := ∫ θ in (0:ℝ)..(π/2), sqrt (1-k^2*sin θ^2)
/--
Defines `ellipticE₁` of type `ℝ` by `(1-k^2)*ellipticK₁ k-k*ellipticK k`.

Use: `chebyshev2.SineContinuum.ellipticE_derivative` uses this definition to establish the
actual derivative at the stated point: `HasDerivAt ellipticE (ellipticE₁ k) k`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.
-/
def ellipticE₁ (k : ℝ) : ℝ := (1-k^2)*ellipticK₁ k-k*ellipticK k

/--
Defines `boundary` of type `ℝ` by `sin θ*cos θ/sqrt (1-k^2*sin θ^2)`.

Use:
`_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary_integral`
uses this definition to establish the identity `(∫ θ in (0:ℝ)..(π/2), boundary₁ k θ)=0`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.
-/
private def boundary (k θ : ℝ) : ℝ := sin θ*cos θ/sqrt (1-k^2*sin θ^2)
/--
Defines `boundary₁` of type `ℝ` by `(cos θ^2-sin θ^2)/sqrt (1-k^2*sin θ^2)+ k^2*sin θ^2*cos
θ^2/sqrt (1-k^2*sin θ^2)^3`.

Use:
`_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary_derivative`
uses this definition to establish the actual derivative at the stated point: `HasDerivAt
(boundary k) (boundary₁ k θ) θ`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.
-/
private def boundary₁ (k θ : ℝ) : ℝ :=
  (cos θ^2-sin θ^2)/sqrt (1-k^2*sin θ^2)+
    k^2*sin θ^2*cos θ^2/sqrt (1-k^2*sin θ^2)^3

/--
The actual derivative at the stated point: `HasDerivAt (boundary k) (boundary₁ k θ) θ`.

Use:
`_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary_integral`
uses this derivative formula to establish the identity `(∫ θ in (0:ℝ)..(π/2), boundary₁ k
θ)=0`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem boundary_derivative (k θ : ℝ) (hk : |k| < 1) :
    HasDerivAt (boundary k) (boundary₁ k θ) θ := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd : HasDerivAt (fun θ : ℝ => 1-k^2*sin θ^2) (-2*k^2*sin θ*cos θ) θ := by
    convert (hasDerivAt_const θ (1:ℝ)).sub (((hasDerivAt_sin θ).pow 2).const_mul (k^2)) using 1
    ring
  have hp := elliptic_den_pos k θ hk
  have hr := hd.sqrt hp.ne'
  have hs := (sqrt_pos.mpr hp).ne'
  have hb := ((hasDerivAt_sin θ).mul (hasDerivAt_cos θ)).div hr hs
  convert hb using 1
  · rfl
  · dsimp [boundary₁]
    field_simp
    ring

/--
Continuity of the displayed function: `Continuous (boundary₁ k)`.

Use:
`_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary_integral`
uses this continuity result to establish the identity `(∫ θ in (0:ℝ)..(π/2), boundary₁ k
θ)=0`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.elliptic_den_pos` with the
arguments shown in the proof.
-/
private theorem boundary₁_continuous (k : ℝ) (hk : |k| < 1) : Continuous (boundary₁ k) := by
  have hs (θ : ℝ) : sqrt (1-k^2*sin θ^2) ≠ 0 := (sqrt_pos.mpr (elliptic_den_pos k θ hk)).ne'
  exact ((by fun_prop : Continuous (fun θ => cos θ^2-sin θ^2)).div (by fun_prop) hs).add
    ((by fun_prop : Continuous (fun θ => k^2*sin θ^2*cos θ^2)).div (by fun_prop)
      (fun θ => pow_ne_zero 3 (hs θ)))

/--
Exact identity `(∫ θ in (0:ℝ)..(π/2), boundary₁ k θ)=0`.

Use: `chebyshev2.SineContinuum.ellipticE_eq` rewrites with this identity to establish exact
identity `ellipticE k=(1-k^2)*(ellipticK k+k*ellipticK₁ k)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary_derivative`,
`_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary₁_continuous`
with the arguments shown in the proof.
-/
private theorem boundary_integral (k : ℝ) (hk : |k| < 1) :
    (∫ θ in (0:ℝ)..(π/2), boundary₁ k θ)=0 := by
  have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => boundary_derivative k θ hk)
    ((boundary₁_continuous k hk).intervalIntegrable (μ := volume) 0 (π/2))
  simpa [boundary] using hb

/--
The precise assertion is `sqrt (1-k^2*sin θ^2)= (1-k^2)*(ellipticIntegrand k
θ+k*ellipticIntegrand₁ k θ)+k^2*boundary₁ k θ`.

Use: `chebyshev2.SineContinuum.ellipticE_eq` uses this identity to establish the identity
`ellipticE k=(1-k^2)*(ellipticK k+k*ellipticK₁ k)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem integrand_identity (k θ : ℝ) (hk : |k| < 1) :
    sqrt (1-k^2*sin θ^2)=
      (1-k^2)*(ellipticIntegrand k θ+k*ellipticIntegrand₁ k θ)+k^2*boundary₁ k θ := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hp := elliptic_den_pos k θ hk
  have hs := (sqrt_pos.mpr hp).ne'
  have hr := sq_sqrt hp.le
  have hc : cos θ^2=1-sin θ^2 := by nlinarith [sin_sq_add_cos_sq θ]
  dsimp [ellipticIntegrand,ellipticIntegrand₁,boundary₁]
  rw [hc]
  generalize sin θ=s at hs hr ⊢
  generalize sqrt (1-k^2*s^2)=r at hs hr ⊢
  field_simp [hs]
  rw [show r^4=(r^2)^2 by ring,hr]
  ring

/--
The first/second elliptic-integral relation is proved by an actual integration-by-parts
boundary term, using chebyshev1's derivative integral.

Exact identity `ellipticE k=(1-k^2)*(ellipticK k+k*ellipticK₁ k)`.

Use: `chebyshev2.SineContinuum.ellipticE_derivative` uses this identity to establish the
actual derivative at the stated point: `HasDerivAt ellipticE (ellipticE₁ k) k`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.elliptic_integrand_continuous`,
`chebyshev1.SineJacobi.ellipticIntegrand₁_continuous`,
`_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary₁_continuous`
with the arguments shown in the proof.
-/
theorem ellipticE_eq (k : ℝ) (hk : |k| < 1) :
    ellipticE k=(1-k^2)*(ellipticK k+k*ellipticK₁ k) := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.elliptic_integrand_continuous`,
  -- `chebyshev1.SineJacobi.ellipticIntegrand₁_continuous`,
  -- `_private.chebyshev2.SineContinuum.EllipticSecond.0.chebyshev2.SineContinuum.boundary₁_continuous`
  -- with the arguments shown in the proof.
  have hi : IntervalIntegrable (ellipticIntegrand k) volume 0 (π/2) :=
    (elliptic_integrand_continuous k hk).intervalIntegrable 0 (π/2)
  have hi₁ := (ellipticIntegrand₁_continuous k hk).intervalIntegrable (μ := volume) 0 (π/2)
  have hb := (boundary₁_continuous k hk).intervalIntegrable (μ := volume) 0 (π/2)
  have he : ellipticE k=∫ θ in (0:ℝ)..(π/2),
      (1-k^2)*(ellipticIntegrand k θ+k*ellipticIntegrand₁ k θ)+k^2*boundary₁ k θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact integrand_identity k θ hk
  rw [he,intervalIntegral.integral_add ((hi.add (hi₁.const_mul k)).const_mul _) (hb.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi (hi₁.const_mul k),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,boundary_integral k hk,
    mul_zero,add_zero]
  rfl

/--
Continuity of the displayed function: `Continuous ellipticE`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` uses this continuity result to
establish convergence along the specified source filter to the specified limit: `Tendsto
ellipticLegendre (𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ellipticE_continuous : Continuous ellipticE := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let F : ℝ → ℝ → ℝ := fun k θ => sqrt (1-k^2*sin θ^2)
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous F.uncurry := by fun_prop
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hc
    (isCompact_Icc (a := (0:ℝ)) (b := π/2))
  have he : ellipticE=(fun k => ∫ θ in Icc (0:ℝ) (π/2), sqrt (1-k^2*sin θ^2)) := by
    funext k
    rw [ellipticE,intervalIntegral.integral_of_le (half_pos pi_pos).le,integral_Icc_eq_integral_Ioc]
  rw [he]
  exact hi

/--
Exact identity `ellipticE 1=1`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto ellipticLegendre
(𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem ellipticE_one : ellipticE 1=1 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have he : ellipticE 1=∫ θ in (0:ℝ)..(π/2), cos θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (half_pos pi_pos).le] at hθ
    change sqrt (1-1^2*sin θ^2)=cos θ
    have hc : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,pi_pos],hθ.2⟩
    have ht : 1-1^2*sin θ^2=cos θ^2 := by nlinarith [sin_sq_add_cos_sq θ]
    rw [ht,sqrt_sq hc]
  rw [he,integral_cos]
  simp

/--
The actual derivative at the stated point: `HasDerivAt ellipticE (ellipticE₁ k) k`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt ellipticLegendre 0 k`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem ellipticE_derivative {k : ℝ} (hk : |k| < 1) : HasDerivAt ellipticE (ellipticE₁ k) k := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hd := ((hasDerivAt_const k (1:ℝ)).sub ((hasDerivAt_id k).pow 2)).mul
    ((ellipticK_deriv hk).add ((hasDerivAt_id k).mul (ellipticK₁_deriv hk)))
  have he : ellipticE =ᶠ[𝓝 k] (fun k => (1-k^2)*(ellipticK k+k*ellipticK₁ k)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hk)] with u hu
    exact ellipticE_eq u (abs_lt.mpr hu)
  have hd' := hd.congr_of_eventuallyEq he
  convert hd' using 1
  dsimp [ellipticE₁]
  linear_combination -(ellipticK_ode hk)

/--
Exact identity `ellipticE k-ellipticK k=k*ellipticE₁ k`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` rewrites with this identity to
establish convergence along the specified source filter to the specified limit: `Tendsto
ellipticLegendre (𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.ellipticE_eq` with the
arguments shown in the proof.
-/
theorem ellipticE_difference (k : ℝ) (hk : |k| < 1) :
    ellipticE k-ellipticK k=k*ellipticE₁ k := by
  rw [ellipticE_eq k hk]
  dsimp [ellipticE₁]
  ring

end
end chebyshev2.SineContinuum
