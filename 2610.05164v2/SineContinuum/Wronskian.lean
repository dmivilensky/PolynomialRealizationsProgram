import «2610.05164v2».SineContinuum.Profiles
import «2610.05164v2».SineContinuum.LegendreIdentity

/-!
Article: 2610.05164v2, Proposition 2.
Lemma 5's exact Wronskian constant, derived from the complementary elliptic identity with its
independently proved endpoint normalization.
Use: `«2610.05164v2».SineContinuum.wronskian_eq_two` feeds
`«2610.05164v2».SineContinuum.ratio_derivative` (ratio derivative).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open «2606.16671v2».SineJacobi Set Real
set_option backward.isDefEq.respectTransparency false

/--
Membership in the specified domain/enclosure: `sqrt 2/2 ∈ Ioo (0:ℝ) 1`.

Use:
`_private.«2610.05164v2».SineContinuum.Wronskian.0.«2610.05164v2».SineContinuum.midpoint_product`
uses this assertion to establish the identity `(sqrt 2/2)*ellipticK (sqrt 2/2)*ellipticK₁
(sqrt 2/2)=π/2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
private theorem half_modulus_mem : sqrt 2/2 ∈ Ioo (0:ℝ) 1 := by
  have hp : 0 < sqrt (2:ℝ) := sqrt_pos.mpr (by norm_num)
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  constructor <;> nlinarith

/--
Exact identity `(sqrt 2/2)^2=(1/2:ℝ)`.

Use:
`_private.«2610.05164v2».SineContinuum.Wronskian.0.«2610.05164v2».SineContinuum.midpoint_product`
rewrites with this identity to establish the identity `(sqrt 2/2)*ellipticK (sqrt
2/2)*ellipticK₁ (sqrt 2/2)=π/2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
private theorem half_modulus_square : (sqrt 2/2)^2=(1/2:ℝ) := by
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

/--
Exact identity `l (1/2)=(2/π)*ellipticK (sqrt 2/2)`.

Use: `«2610.05164v2».SineContinuum.wronskian_eq_two` rewrites with this identity to establish
exact identity `wronskian t=2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l_formula`,
`«2610.05164v2».SineJacobi.ellipticK_square` with the arguments shown in the proof.
-/
theorem l_midpoint : l (1/2)=(2/π)*ellipticK (sqrt 2/2) := by
  rw [l_formula,SineJacobi.ellipticK_square]
  rw [show π*(1/2)=π/2 by ring,show π/2/2=π/4 by ring,sin_pi_div_two,sqrt_one,
    sin_pi_div_four,mul_one]

/--
Exact identity `l₁ (1/2)=(sqrt 2/2)*ellipticK₁ (sqrt 2/2)`.

Use: `«2610.05164v2».SineContinuum.wronskian_eq_two` rewrites with this identity to establish
exact identity `wronskian t=2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem l₁_midpoint : l₁ (1/2)=(sqrt 2/2)*ellipticK₁ (sqrt 2/2) := by
  dsimp [l₁,sineProfile₁,profileWeight₁,profileWeight,profileElliptic,profileElliptic₁,
    profileModulus,profileModulus₁]
  rw [show π*(1/2)=π/2 by ring,show π/2/2=π/4 by ring,
    cos_pi_div_two,sin_pi_div_two,sin_pi_div_four,cos_pi_div_four,sqrt_one]
  field_simp [(sqrt_pos.mpr pi_pos).ne']
  ring

/--
Exact identity `(sqrt 2/2)*ellipticK (sqrt 2/2)*ellipticK₁ (sqrt 2/2)=π/2`.

Use: `«2610.05164v2».SineContinuum.wronskian_eq_two` uses this identity to establish exact
identity `wronskian t=2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.Wronskian.0.«2610.05164v2».SineContinuum.half_modulus_mem`,
`_private.«2610.05164v2».SineContinuum.Wronskian.0.«2610.05164v2».SineContinuum.half_modulus_square`,
`«2610.05164v2».SineContinuum.ellipticLegendre_identity` with the arguments shown in the proof.
-/
private theorem midpoint_product :
    (sqrt 2/2)*ellipticK (sqrt 2/2)*ellipticK₁ (sqrt 2/2)=π/2 := by
  -- Apply
  -- `_private.«2610.05164v2».SineContinuum.Wronskian.0.«2610.05164v2».SineContinuum.half_modulus_mem`,
  -- `«2610.05164v2».SineContinuum.complementary`,
  -- `_private.«2610.05164v2».SineContinuum.Wronskian.0.«2610.05164v2».SineContinuum.half_modulus_square`
  -- to the displayed hypotheses, then match the resulting expression to the goal.
  have hk := half_modulus_mem
  have hk' : |sqrt (2:ℝ)/2| < 1 := by rw [abs_of_pos hk.1]; exact hk.2
  have hc : complementary (sqrt 2/2)=sqrt 2/2 := by
    rw [complementary,show 1-(sqrt 2/2)^2=(sqrt 2/2)^2 by rw [half_modulus_square]; norm_num,
      sqrt_sq hk.1.le]
  have h := ellipticLegendre_identity hk
  dsimp [ellipticLegendre] at h
  rw [hc,ellipticE_eq _ hk',half_modulus_square] at h
  nlinarith [h]

/--
Lemma 5's exact Wronskian constant, derived from the complementary elliptic identity with its
independently proved endpoint normalization.

Exact identity `wronskian t=2`.

Use: `«2610.05164v2».SineContinuum.X_derivative` uses this identity to establish the actual
derivative at the stated point: `HasDerivAt X (SineJacobi.phi t)⁻¹ t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem wronskian_eq_two {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : wronskian t=2 := by
  rw [wronskian_constant ht]
  dsimp [wronskian,r,r₁]
  rw [show (1:ℝ)-1/2=1/2 by ring,l_midpoint,l₁_midpoint]
  field_simp
  linear_combination 4*midpoint_product

end
end «2610.05164v2».SineContinuum
