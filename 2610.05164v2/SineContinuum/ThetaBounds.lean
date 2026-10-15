import «2610.05164v2».SineContinuum.ThetaSeries

/-!
Article: 2610.05164v2, Proposition 2.
Uniform logarithmic remainder bounds; `n_log_bounds` transfers them to the actual density using the
proved theta identity.
Use: `«2610.05164v2».SineContinuum.thetaDensity_log_bounds` feeds
`«2610.05164v2».SineContinuum.n_log_bounds` (Explicit bounded remainder in the actual sine-density
logarithmic tail).
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency true

/--
Defines `thetaRho` of type `ℝ` by `exp (2*|x|)`.

Use: `«2610.05164v2».SineContinuum.thetaDensity` uses this definition in the displayed
construction of `thetaDensity`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaRho (x : ℝ) : ℝ := exp (2*|x|)
/--
Defines `thetaNome` of type `ℝ` by `exp (-π*thetaRho x)`.

Use: `«2610.05164v2».SineContinuum.thetaDensity` uses this definition in the displayed
construction of `thetaDensity`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaNome (x : ℝ) : ℝ := exp (-π*thetaRho x)

/--
The stated quantitative bound `1 ≤ thetaRho x`.

Use: `«2610.05164v2».SineContinuum.thetaNome_small` uses this bound to establish the stated
quantitative bound `thetaNome x ≤ 1/4`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem thetaRho_ge_one (x : ℝ) : 1 ≤ thetaRho x := one_le_exp (by positivity)
/--
The stated quantitative bound `0 < thetaRho x`.

Use: `«2610.05164v2».SineContinuum.thetaDensity_envelope` uses this bound to establish the
stated quantitative bound `(8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ thetaDensity x ∧
thetaDensity x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem thetaRho_positive (x : ℝ) : 0 < thetaRho x := exp_pos _
/--
The stated quantitative bound `0 < thetaNome x`.

Use: `«2610.05164v2».SineContinuum.thetaDensity_envelope` uses this bound to establish the
stated quantitative bound `(8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ thetaDensity x ∧
thetaDensity x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem thetaNome_positive (x : ℝ) : 0 < thetaNome x := exp_pos _

/--
The stated quantitative bound `thetaNome x ≤ 1/4`.

Use: `«2610.05164v2».SineContinuum.thetaDensity_envelope` uses this bound to establish the
stated quantitative bound `(8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ thetaDensity x ∧
thetaDensity x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaRho_ge_one` with the
arguments shown in the proof.
-/
theorem thetaNome_small (x : ℝ) : thetaNome x ≤ 1/4 := by
  have hp : 3 ≤ π*thetaRho x := by nlinarith [pi_gt_three,thetaRho_ge_one x]
  have he : 4 ≤ exp (π*thetaRho x) := by linarith [add_one_le_exp (π*thetaRho x)]
  rw [thetaNome,show -π*thetaRho x=-(π*thetaRho x) by ring,exp_neg]
  rw [← one_div]
  exact one_div_le_one_div_of_le (by norm_num) he

/--
The right-hand side printed in (10), identified with the actual density by `n_theta` in
`ThetaIdentity`.

Use: `«2610.05164v2».SineContinuum.thetaDensity_envelope` uses this definition to establish the
stated quantitative bound `(8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ thetaDensity x ∧
thetaDensity x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2))`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaDensity (x : ℝ) : ℝ := 8*thetaRho x*exp (-π*thetaRho x/2)*
  sigma₁ (thetaNome x)^2*sigma₂ (thetaNome x)^2

/--
The stated quantitative bound `(8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ thetaDensity x ∧
thetaDensity x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2))`.

Use: `«2610.05164v2».SineContinuum.thetaDensity_log_bounds` uses this bound to establish the
stated quantitative bound `log (8/9:ℝ) ≤ log (thetaDensity x)+π/2*thetaRho x-2*|x| ∧ log
(thetaDensity x)+π/2*thetaRho x-2*|x| ≤ log (40:ℝ)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta_envelope`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sigma_bounds`,
`«2610.05164v2».SineContinuum.thetaNome_positive`,
`«2610.05164v2».SineContinuum.thetaNome_small` with the arguments shown in the proof.
-/
theorem thetaDensity_envelope (x : ℝ) :
    (8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ thetaDensity x ∧
      thetaDensity x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2)) := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.sigma_bounds`,
  -- `«2610.05164v2».SineContinuum.thetaNome_positive`,
  -- `«2610.05164v2».SineContinuum.thetaNome_small` with the arguments shown in the proof.
  obtain ⟨h₁,h₂,h₃,h₄⟩ := sigma_bounds (thetaNome_positive x).le (thetaNome_small x)
  have ha : 1 ≤ sigma₁ (thetaNome x)^2 := by nlinarith
  have hb : 1/9 ≤ sigma₂ (thetaNome x)^2 := by nlinarith
  have hc : sigma₁ (thetaNome x)^2 ≤ 16/9 := by nlinarith
  have hd : sigma₂ (thetaNome x)^2 ≤ 25/9 := by nlinarith
  have hl : 1/9 ≤ sigma₁ (thetaNome x)^2*sigma₂ (thetaNome x)^2 := by
    nlinarith [mul_le_mul ha hb (by norm_num) (sq_nonneg (sigma₁ (thetaNome x)))]
  have hu : sigma₁ (thetaNome x)^2*sigma₂ (thetaNome x)^2 ≤ 5 := by
    nlinarith [mul_le_mul hc hd (sq_nonneg (sigma₂ (thetaNome x))) (by norm_num)]
  have hp : 0 ≤ thetaRho x*exp (-π*thetaRho x/2) :=
    mul_nonneg (thetaRho_positive x).le (exp_pos _).le
  constructor
  · calc
      _ = (8*(thetaRho x*exp (-π*thetaRho x/2)))*(1/9) := by ring
      _ ≤ (8*(thetaRho x*exp (-π*thetaRho x/2)))*
          (sigma₁ (thetaNome x)^2*sigma₂ (thetaNome x)^2) :=
        mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num) hp)
      _ = _ := by unfold thetaDensity; ring
  · calc
      _ = (8*(thetaRho x*exp (-π*thetaRho x/2)))*
          (sigma₁ (thetaNome x)^2*sigma₂ (thetaNome x)^2) := by unfold thetaDensity; ring
      _ ≤ (8*(thetaRho x*exp (-π*thetaRho x/2)))*5 :=
        mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num) hp)
      _ = _ := by ring

/--
The stated quantitative bound `0 < thetaDensity x`.

Use: `«2610.05164v2».SineContinuum.thetaDensity_log_bounds` uses this bound to establish the
stated quantitative bound `log (8/9:ℝ) ≤ log (thetaDensity x)+π/2*thetaRho x-2*|x| ∧ log
(thetaDensity x)+π/2*thetaRho x-2*|x| ≤ log (40:ℝ)`.

Article: 2610.05164v2, Proposition 2 via
`«2610.05164v2».SineContinuum.thetaDensity_log_bounds`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaRho_positive`,
`«2610.05164v2».SineContinuum.thetaDensity_envelope` with the arguments shown in the proof.
-/
theorem thetaDensity_positive (x : ℝ) : 0 < thetaDensity x :=
  (mul_pos (by norm_num : (0:ℝ)<8/9)
    (mul_pos (thetaRho_positive x) (exp_pos _))).trans_le (thetaDensity_envelope x).1

/--
Uniform logarithmic remainder bounds; `n_log_bounds` transfers them to the actual density using
the proved theta identity.

The stated quantitative bound `log (8/9:ℝ) ≤ log (thetaDensity x)+π/2*thetaRho x-2*|x| ∧ log
(thetaDensity x)+π/2*thetaRho x-2*|x| ≤ log (40:ℝ)`.

Use: `«2610.05164v2».SineContinuum.n_log_bounds` uses this bound to establish the stated
quantitative bound `log (8/9:ℝ) ≤ log (n x)+π/2*exp (2*|x|)-2*|x| ∧ log (n x)+π/2*exp
(2*|x|)-2*|x| ≤ log (40:ℝ)`.

Article: 2610.05164v2, Proposition 2.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaRho_positive`,
`«2610.05164v2».SineContinuum.thetaDensity_envelope`,
`«2610.05164v2».SineContinuum.thetaDensity_positive` with the arguments shown in the proof.
-/
theorem thetaDensity_log_bounds (x : ℝ) :
    log (8/9:ℝ) ≤ log (thetaDensity x)+π/2*thetaRho x-2*|x| ∧
      log (thetaDensity x)+π/2*thetaRho x-2*|x| ≤ log (40:ℝ) := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.thetaRho_positive`,
  -- `«2610.05164v2».SineContinuum.thetaDensity_envelope`,
  -- `«2610.05164v2».SineContinuum.thetaDensity_positive` with the arguments shown in the
  -- proof.
  have hp : 0 < thetaRho x*exp (-π*thetaRho x/2) :=
    mul_pos (thetaRho_positive x) (exp_pos _)
  have h₁ := log_le_log (mul_pos (by norm_num : (0:ℝ)<8/9) hp) (thetaDensity_envelope x).1
  have h₂ := log_le_log (thetaDensity_positive x) (thetaDensity_envelope x).2
  rw [log_mul (by norm_num : (8/9:ℝ) ≠ 0) hp.ne',
    log_mul (thetaRho_positive x).ne' (exp_pos _).ne',log_exp] at h₁
  rw [log_mul (by norm_num : (40:ℝ) ≠ 0) hp.ne',
    log_mul (thetaRho_positive x).ne' (exp_pos _).ne',log_exp] at h₂
  have hr : log (thetaRho x)=2*|x| := log_exp _
  rw [hr] at h₁ h₂
  constructor <;> linarith

end
end «2610.05164v2».SineContinuum
