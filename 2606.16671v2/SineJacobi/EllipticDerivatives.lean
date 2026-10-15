import «2606.16671v2».SineJacobi.Profile
import «2606.16671v2».Analysis.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: 2606.16671v2, Theorem E.3.
Elliptic Derivatives.
Use: `«2606.16671v2».SineJacobi.ellipticK₁_deriv` feeds
`«2610.05164v2».SineContinuum.ellipticE_derivative` (elliptic E derivative).
Proof chain: `«2606.16671v2».SineJacobi.sineProfile_ode` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set

/--
Defines `ellipticIntegrand` of type `ℝ` by `1/Real.sqrt (1-k^2*sin theta^2)`.

Use: `«2606.16671v2».SineJacobi.ellipticK_deriv` uses this definition to establish the actual
derivative at the stated point: `HasDerivAt ellipticK (ellipticK₁ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.
-/
def ellipticIntegrand (k theta : ℝ) : ℝ := 1/Real.sqrt (1-k^2*sin theta^2)
/--
Defines `ellipticIntegrand₁` of type `ℝ` by `k*sin theta^2/Real.sqrt (1-k^2*sin theta^2)^3`.

Use: `«2606.16671v2».SineJacobi.ellipticIntegrand_deriv` uses this definition to establish the
actual derivative at the stated point: `HasDerivAt (fun u => ellipticIntegrand u theta)
(ellipticIntegrand₁ k theta) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.
-/
def ellipticIntegrand₁ (k theta : ℝ) : ℝ :=
  k*sin theta^2/Real.sqrt (1-k^2*sin theta^2)^3
/--
Defines `ellipticIntegrand₂` of type `ℝ` by `sin theta^2/Real.sqrt (1-k^2*sin theta^2)^3 +
3*k^2*sin theta^4/Real.sqrt (1-k^2*sin theta^2)^5`.

Use: `«2606.16671v2».SineJacobi.ellipticIntegrand₁_deriv` uses this definition to establish the
actual derivative at the stated point: `HasDerivAt (fun u => ellipticIntegrand₁ u theta)
(ellipticIntegrand₂ k theta) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.
-/
def ellipticIntegrand₂ (k theta : ℝ) : ℝ :=
  sin theta^2/Real.sqrt (1-k^2*sin theta^2)^3 +
    3*k^2*sin theta^4/Real.sqrt (1-k^2*sin theta^2)^5
/--
Defines `ellipticK₁` of type `ℝ` by `∫ theta in (0:ℝ)..(Real.pi/2), ellipticIntegrand₁ k
theta`.

Use: `«2606.16671v2».SineJacobi.ellipticK_deriv` uses this definition to establish the actual
derivative at the stated point: `HasDerivAt ellipticK (ellipticK₁ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.
-/
def ellipticK₁ (k : ℝ) : ℝ := ∫ theta in (0:ℝ)..(Real.pi/2), ellipticIntegrand₁ k theta
/--
Defines `ellipticK₂` of type `ℝ` by `∫ theta in (0:ℝ)..(Real.pi/2), ellipticIntegrand₂ k
theta`.

Use: `«2606.16671v2».SineJacobi.ellipticK₁_deriv` uses this definition to establish the actual
derivative at the stated point: `HasDerivAt ellipticK₁ (ellipticK₂ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.
-/
def ellipticK₂ (k : ℝ) : ℝ := ∫ theta in (0:ℝ)..(Real.pi/2), ellipticIntegrand₂ k theta

/--
The stated quantitative bound `0 < 1-k^2*sin theta^2`.

Use: `«2606.16671v2».SineJacobi.ellipticIntegrand_deriv` uses this bound to establish the
actual derivative at the stated point: `HasDerivAt (fun u => ellipticIntegrand u theta)
(ellipticIntegrand₁ k theta) k`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_le_four_div_pi`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_lower` with the
arguments shown in the proof.
-/
theorem elliptic_den_pos (k theta : ℝ) (hk : |k| < 1) : 0 < 1-k^2*sin theta^2 := by
  have hp : 0 < 1-k^2 := by have hb := abs_lt.mp hk; nlinarith
  exact lt_of_lt_of_le hp (elliptic_den_lower k theta)

/--
The actual derivative at the stated point: `HasDerivAt (fun u => ellipticIntegrand u theta)
(ellipticIntegrand₁ k theta) k`.

Use: `«2606.16671v2».SineJacobi.ellipticK_deriv` uses this derivative formula to establish the
actual derivative at the stated point: `HasDerivAt ellipticK (ellipticK₁ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem ellipticIntegrand_deriv (k theta : ℝ) (hk : |k| < 1) :
    HasDerivAt (fun u => ellipticIntegrand u theta) (ellipticIntegrand₁ k theta) k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd : HasDerivAt (fun u : ℝ => 1-u^2*sin theta^2) (-2*k*sin theta^2) k := by
    convert (hasDerivAt_const k (1:ℝ)).sub (((hasDerivAt_id k).pow 2).mul_const (sin theta^2)) using 1
    · funext u; simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]; ring
  have hp := elliptic_den_pos k theta hk
  have hr := hd.sqrt hp.ne'
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have hb := (hasDerivAt_const k (1:ℝ)).div hr hs
  convert hb using 1
  · rfl
  · unfold ellipticIntegrand₁
    simp only [one_mul]
    generalize Real.sqrt (1-k^2*sin theta^2) = r at hs ⊢
    field_simp [hs]
    ring

/--
The actual derivative at the stated point: `HasDerivAt (fun u => ellipticIntegrand₁ u theta)
(ellipticIntegrand₂ k theta) k`.

Use: `«2606.16671v2».SineJacobi.ellipticK₁_deriv` uses this derivative formula to establish the
actual derivative at the stated point: `HasDerivAt ellipticK₁ (ellipticK₂ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem ellipticIntegrand₁_deriv (k theta : ℝ) (hk : |k| < 1) :
    HasDerivAt (fun u => ellipticIntegrand₁ u theta) (ellipticIntegrand₂ k theta) k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd : HasDerivAt (fun u : ℝ => 1-u^2*sin theta^2) (-2*k*sin theta^2) k := by
    convert (hasDerivAt_const k (1:ℝ)).sub (((hasDerivAt_id k).pow 2).mul_const (sin theta^2)) using 1
    · funext u; simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]; ring
  have hp := elliptic_den_pos k theta hk
  have hr := hd.sqrt hp.ne'
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have hb := ((hasDerivAt_id k).mul_const (sin theta^2)).div (hr.pow 3) (pow_ne_zero 3 hs)
  convert hb using 1
  · rfl
  · unfold ellipticIntegrand₂
    simp only [Pi.pow_apply, id_eq, one_mul]
    generalize Real.sqrt (1-k^2*sin theta^2) = r at hs ⊢
    field_simp [hs]
    ring

/--
Continuity of the displayed function: `Continuous (ellipticIntegrand₁ k)`.

Use: `«2606.16671v2».SineJacobi.ellipticK₁_deriv` uses this continuity result to establish the
actual derivative at the stated point: `HasDerivAt ellipticK₁ (ellipticK₂ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_pos` with the
arguments shown in the proof.
-/
theorem ellipticIntegrand₁_continuous (k : ℝ) (hk : |k| < 1) :
    Continuous (ellipticIntegrand₁ k) := by
  unfold ellipticIntegrand₁
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro theta
  exact pow_ne_zero 3 (Real.sqrt_pos.mpr (elliptic_den_pos k theta hk)).ne'

/--
Continuity of the displayed function: `Continuous (ellipticIntegrand₂ k)`.

Use: `«2606.16671v2».SineJacobi.ellipticK_ode` uses this continuity result to establish exact
identity `k*(1-k^2)*ellipticK₂ k + (1-3*k^2)*ellipticK₁ k - k*ellipticK k = 0`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_pos` with the
arguments shown in the proof.
-/
theorem ellipticIntegrand₂_continuous (k : ℝ) (hk : |k| < 1) :
    Continuous (ellipticIntegrand₂ k) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_pos` with the
  -- arguments shown in the proof.
  unfold ellipticIntegrand₂
  apply Continuous.add
  · apply Continuous.div (by fun_prop) (by fun_prop)
    intro theta
    exact pow_ne_zero 3 (Real.sqrt_pos.mpr (elliptic_den_pos k theta hk)).ne'
  · apply Continuous.div (by fun_prop) (by fun_prop)
    intro theta
    exact pow_ne_zero 5 (Real.sqrt_pos.mpr (elliptic_den_pos k theta hk)).ne'

/--
Continuity on the stated domain: `ContinuousOn ellipticIntegrand₁.uncurry (Icc (-r) r ×ˢ Icc
(0:ℝ) (Real.pi/2))`.

Use: `«2606.16671v2».SineJacobi.ellipticK_deriv` uses this continuity result to establish the
actual derivative at the stated point: `HasDerivAt ellipticK (ellipticK₁ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_pos` with the
arguments shown in the proof.
-/
theorem ellipticIntegrand₁_rectangle {r : ℝ} (hr : r < 1) :
    ContinuousOn ellipticIntegrand₁.uncurry (Icc (-r) r ×ˢ Icc (0:ℝ) (Real.pi/2)) := by
  unfold ellipticIntegrand₁ Function.uncurry
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro p hp
  have hk : |p.1| < 1 := (abs_le.mpr hp.1).trans_lt hr
  exact pow_ne_zero 3 (Real.sqrt_pos.mpr (elliptic_den_pos _ _ hk)).ne'

/--
Continuity on the stated domain: `ContinuousOn ellipticIntegrand₂.uncurry (Icc (-r) r ×ˢ Icc
(0:ℝ) (Real.pi/2))`.

Use: `«2606.16671v2».SineJacobi.ellipticK₁_deriv` uses this continuity result to establish the
actual derivative at the stated point: `HasDerivAt ellipticK₁ (ellipticK₂ k) k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_pos` with the
arguments shown in the proof.
-/
theorem ellipticIntegrand₂_rectangle {r : ℝ} (hr : r < 1) :
    ContinuousOn ellipticIntegrand₂.uncurry (Icc (-r) r ×ˢ Icc (0:ℝ) (Real.pi/2)) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_pos` with the
  -- arguments shown in the proof.
  unfold ellipticIntegrand₂ Function.uncurry
  apply ContinuousOn.add
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    have hk : |p.1| < 1 := (abs_le.mpr hp.1).trans_lt hr
    exact pow_ne_zero 3 (Real.sqrt_pos.mpr (elliptic_den_pos _ _ hk)).ne'
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp
    have hk : |p.1| < 1 := (abs_le.mpr hp.1).trans_lt hr
    exact pow_ne_zero 5 (Real.sqrt_pos.mpr (elliptic_den_pos _ _ hk)).ne'

/--
The actual derivative at the stated point: `HasDerivAt ellipticK (ellipticK₁ k) k`.

Use: `«2606.16671v2».SineJacobi.profileElliptic_deriv` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt profileElliptic
(profileElliptic₁ t) t`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.hasDerivAt_integral_rectangle`,
`«2606.16671v2».SineJacobi.elliptic_integrand_continuous`,
`«2606.16671v2».SineJacobi.ellipticIntegrand₁_rectangle` with the arguments shown in the proof.
-/
theorem ellipticK_deriv {k : ℝ} (hk : |k| < 1) : HasDerivAt ellipticK (ellipticK₁ k) k := by
  -- Use the identities/estimates `«2606.16671v2».Analysis.hasDerivAt_integral_rectangle`,
  -- `«2606.16671v2».SineJacobi.elliptic_integrand_continuous`,
  -- `«2606.16671v2».SineJacobi.ellipticIntegrand₁_rectangle` with the arguments shown in the
  -- proof.
  let r := (|k|+1)/2
  have hr : r < 1 := by dsimp [r]; linarith
  have hkr : |k| < r := by dsimp [r]; linarith
  have hx : k ∈ Ioo (-r) r := abs_lt.mp hkr
  exact Analysis.hasDerivAt_integral_rectangle ellipticIntegrand ellipticIntegrand₁
    hx (half_pos pi_pos).le
    (by
      intro u hu
      exact (elliptic_integrand_continuous u ((abs_le.mpr hu).trans_lt hr)).continuousOn)
    (ellipticIntegrand₁_rectangle hr)
    (by intro u hu theta _; exact ellipticIntegrand_deriv u theta ((abs_le.mpr hu).trans_lt hr))

/--
The actual derivative at the stated point: `HasDerivAt ellipticK₁ (ellipticK₂ k) k`.

Use: `«2606.16671v2».SineJacobi.profileElliptic₁_deriv` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt profileElliptic₁
(profileElliptic₂ t) t`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_ode`.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.hasDerivAt_integral_rectangle`,
`«2606.16671v2».SineJacobi.ellipticIntegrand₁_continuous`,
`«2606.16671v2».SineJacobi.ellipticIntegrand₂_rectangle` with the arguments shown in the proof.
-/
theorem ellipticK₁_deriv {k : ℝ} (hk : |k| < 1) : HasDerivAt ellipticK₁ (ellipticK₂ k) k := by
  -- Use the identities/estimates `«2606.16671v2».Analysis.hasDerivAt_integral_rectangle`,
  -- `«2606.16671v2».SineJacobi.ellipticIntegrand₁_continuous`,
  -- `«2606.16671v2».SineJacobi.ellipticIntegrand₂_rectangle` with the arguments shown in the
  -- proof.
  let r := (|k|+1)/2
  have hr : r < 1 := by dsimp [r]; linarith
  have hkr : |k| < r := by dsimp [r]; linarith
  have hx : k ∈ Ioo (-r) r := abs_lt.mp hkr
  exact Analysis.hasDerivAt_integral_rectangle ellipticIntegrand₁ ellipticIntegrand₂
    hx (half_pos pi_pos).le
    (by
      intro u hu
      exact (ellipticIntegrand₁_continuous u ((abs_le.mpr hu).trans_lt hr)).continuousOn)
    (ellipticIntegrand₂_rectangle hr)
    (by intro u hu theta _; exact ellipticIntegrand₁_deriv u theta ((abs_le.mpr hu).trans_lt hr))

end
end «2606.16671v2».SineJacobi
