import chebyshev1.SineJacobi.EllipticDerivatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: chebyshev1, Theorem E.3.
The elliptic integral satisfies the complete second-order equation on |k|<1.
Use: `chebyshev1.SineJacobi.ellipticK_ode` feeds
`chebyshev1.SineJacobi.sineProfile_explicit_ode` (sine Profile explicit ode).
Proof chain: `chebyshev1.SineJacobi.sineProfile_ode` — chebyshev1, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
Source: NIST Digital Library of Mathematical Functions, Chapter 19 — complete elliptic integral
differential equation. The needed form is proved here.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set MeasureTheory

/--
Defines `ellipticBoundary` of type `ℝ` by `sin theta*cos theta/Real.sqrt (1-k^2*sin
theta^2)^3`.

Use: `chebyshev1.SineJacobi.ellipticBoundary_integral` uses this definition to establish
exact identity `(∫ theta in (0:ℝ)..(Real.pi/2), ellipticBoundary₁ k theta) = 0`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — complete elliptic integral
differential equation.
-/
def ellipticBoundary (k theta : ℝ) : ℝ :=
  sin theta*cos theta/Real.sqrt (1-k^2*sin theta^2)^3
/--
Defines `ellipticBoundary₁` of type `ℝ` by `(cos theta^2-sin theta^2)/Real.sqrt (1-k^2*sin
theta^2)^3 + 3*k^2*sin theta^2*cos theta^2/Real.sqrt (1-k^2*sin theta^2)^5`.

Use: `chebyshev1.SineJacobi.ellipticBoundary_deriv` uses this definition to establish the
actual derivative at the stated point: `HasDerivAt (ellipticBoundary k) (ellipticBoundary₁ k
theta) theta`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — complete elliptic integral
differential equation.
-/
def ellipticBoundary₁ (k theta : ℝ) : ℝ :=
  (cos theta^2-sin theta^2)/Real.sqrt (1-k^2*sin theta^2)^3 +
    3*k^2*sin theta^2*cos theta^2/Real.sqrt (1-k^2*sin theta^2)^5

/--
The actual derivative at the stated point: `HasDerivAt (ellipticBoundary k) (ellipticBoundary₁
k theta) theta`.

Use: `chebyshev1.SineJacobi.ellipticBoundary_integral` uses this derivative formula to
establish exact identity `(∫ theta in (0:ℝ)..(Real.pi/2), ellipticBoundary₁ k theta) = 0`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — complete elliptic integral
differential equation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ellipticBoundary_deriv (k theta : ℝ) (hk : |k| < 1) :
    HasDerivAt (ellipticBoundary k) (ellipticBoundary₁ k theta) theta := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd : HasDerivAt (fun theta : ℝ => 1-k^2*sin theta^2)
      (-2*k^2*sin theta*cos theta) theta := by
    convert (hasDerivAt_const theta (1:ℝ)).sub
      (((hasDerivAt_sin theta).pow 2).const_mul (k^2)) using 1 ; ring
  have hp := elliptic_den_pos k theta hk
  have hr := hd.sqrt hp.ne'
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have hb := ((hasDerivAt_sin theta).mul (hasDerivAt_cos theta)).div
    (hr.pow 3) (pow_ne_zero 3 hs)
  convert hb using 1
  · rfl
  · unfold ellipticBoundary₁
    simp only [Pi.pow_apply, Pi.mul_apply]
    generalize Real.sqrt (1-k^2*sin theta^2) = r at hs ⊢
    field_simp [hs]
    ring

/--
Exact identity `k*(1-k^2)*ellipticIntegrand₂ k theta + (1-3*k^2)*ellipticIntegrand₁ k theta -
k*ellipticIntegrand k theta = -k*ellipticBoundary₁ k theta`.

Use: `chebyshev1.SineJacobi.ellipticK_ode` rewrites with this identity to establish exact
identity `k*(1-k^2)*ellipticK₂ k + (1-3*k^2)*ellipticK₁ k - k*ellipticK k = 0`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — complete elliptic integral
differential equation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem elliptic_ode_integrand (k theta : ℝ) (hk : |k| < 1) :
    k*(1-k^2)*ellipticIntegrand₂ k theta +
      (1-3*k^2)*ellipticIntegrand₁ k theta - k*ellipticIntegrand k theta =
        -k*ellipticBoundary₁ k theta := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hp := elliptic_den_pos k theta hk
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have hroot := Real.sq_sqrt hp.le
  have hcos : cos theta^2 = 1-sin theta^2 := by nlinarith [sin_sq_add_cos_sq theta]
  unfold ellipticIntegrand ellipticIntegrand₁ ellipticIntegrand₂ ellipticBoundary₁
  rw [hcos]
  generalize sin theta = s at hroot hs ⊢
  generalize Real.sqrt (1-k^2*s^2) = r at hroot hs ⊢
  field_simp [hs]
  rw [show r^4 = (r^2)^2 by ring, hroot]
  ring

/--
Exact identity `(∫ theta in (0:ℝ)..(Real.pi/2), ellipticBoundary₁ k theta) = 0`.

Use: `chebyshev1.SineJacobi.ellipticK_ode` rewrites with this identity to establish exact
identity `k*(1-k^2)*ellipticK₂ k + (1-3*k^2)*ellipticK₁ k - k*ellipticK k = 0`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — complete elliptic integral
differential equation.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.elliptic_den_pos`,
`chebyshev1.SineJacobi.ellipticBoundary_deriv` with the arguments shown in the proof.
-/
theorem ellipticBoundary_integral (k : ℝ) (hk : |k| < 1) :
    (∫ theta in (0:ℝ)..(Real.pi/2), ellipticBoundary₁ k theta) = 0 := by
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (ellipticBoundary₁ k) := by
    unfold ellipticBoundary₁
    apply Continuous.add
    · apply Continuous.div (by fun_prop) (by fun_prop)
      intro theta
      exact pow_ne_zero 3 (Real.sqrt_pos.mpr (elliptic_den_pos k theta hk)).ne'
    · apply Continuous.div (by fun_prop) (by fun_prop)
      intro theta
      exact pow_ne_zero 5 (Real.sqrt_pos.mpr (elliptic_den_pos k theta hk)).ne'
  have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _ => ellipticBoundary_deriv k theta hk)
    (hc.intervalIntegrable (μ := volume) 0 (Real.pi/2))
  simpa [ellipticBoundary] using hb

/--
The elliptic integral satisfies the complete second-order equation on |k|<1.

Exact identity `k*(1-k^2)*ellipticK₂ k + (1-3*k^2)*ellipticK₁ k - k*ellipticK k = 0`.

Use: `chebyshev1.SineJacobi.sineProfile_explicit_ode` uses this identity to establish exact
identity `sineProfile₂ t + Real.pi^2/(4*sin (Real.pi*t)^2)*sineProfile t = 0`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_ode`.

Source: NIST Digital Library of Mathematical Functions, Chapter 19 — complete elliptic integral
differential equation.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.elliptic_integrand_continuous`,
`chebyshev1.SineJacobi.ellipticIntegrand₁_continuous`,
`chebyshev1.SineJacobi.ellipticIntegrand₂_continuous` with the arguments shown in the
proof.
-/
theorem ellipticK_ode {k : ℝ} (hk : |k| < 1) :
    k*(1-k^2)*ellipticK₂ k + (1-3*k^2)*ellipticK₁ k - k*ellipticK k = 0 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.elliptic_integrand_continuous`,
  -- `chebyshev1.SineJacobi.ellipticIntegrand₁_continuous`,
  -- `chebyshev1.SineJacobi.ellipticIntegrand₂_continuous` with the arguments shown in the
  -- proof.
  have h0 := (elliptic_integrand_continuous k hk).intervalIntegrable
    (μ := volume) 0 (Real.pi/2)
  change IntervalIntegrable (ellipticIntegrand k) volume 0 (Real.pi/2) at h0
  have h1 := (ellipticIntegrand₁_continuous k hk).intervalIntegrable
    (μ := volume) 0 (Real.pi/2)
  have h2 := (ellipticIntegrand₂_continuous k hk).intervalIntegrable
    (μ := volume) 0 (Real.pi/2)
  have he : k*(1-k^2)*ellipticK₂ k + (1-3*k^2)*ellipticK₁ k - k*ellipticK k =
      ∫ theta in (0:ℝ)..(Real.pi/2),
        (k*(1-k^2)*ellipticIntegrand₂ k theta +
          (1-3*k^2)*ellipticIntegrand₁ k theta - k*ellipticIntegrand k theta) := by
    rw [intervalIntegral.integral_sub ((h2.const_mul _).add (h1.const_mul _)) (h0.const_mul _),
      intervalIntegral.integral_add (h2.const_mul _) (h1.const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
    rfl
  rw [he]
  simp_rw [elliptic_ode_integrand k _ hk]
  rw [intervalIntegral.integral_const_mul, ellipticBoundary_integral k hk, mul_zero]

end
end chebyshev1.SineJacobi
