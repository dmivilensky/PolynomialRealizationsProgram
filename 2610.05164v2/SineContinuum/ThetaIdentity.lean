import «2610.05164v2».SineContinuum.ThetaCoordinate

/-!
Article: 2610.05164v2, Proposition 2.
Explicit bounded remainder in the actual sine-density logarithmic tail.
Use: `«2610.05164v2».SineContinuum.n_theta_envelope` feeds
`«2610.05164v2».LocalObstruction.sine_amplitude_exp_decay` (sine amplitude exp decay).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/--
Proposition 2, equation (10): the actual sine density has the literal theta formula.

Exact identity `n x = thetaDensity x`.

Use: `«2610.05164v2».SineContinuum.n_log_bounds` rewrites with this identity to establish the
stated quantitative bound `log (8/9:ℝ) ≤ log (n x)+π/2*exp (2*|x|)-2*|x| ∧ log (n x)+π/2*exp
(2*|x|)-2*|x| ≤ log (40:ℝ)`.

Article: 2610.05164v2, Proposition 2.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.thetaRho_positive`,
`«2610.05164v2».SineContinuum.thetaPoint_coordinate`, `«2610.05164v2».SineContinuum.n_X` with
the arguments shown in the proof.
-/
theorem n_theta (x : ℝ) : n x = thetaDensity x := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.thetaRho_positive`,
  -- `«2610.05164v2».SineContinuum.thetaPoint_coordinate`, `«2610.05164v2».SineContinuum.n_X`
  -- with the arguments shown in the proof.
  let v := thetaRho x
  have hv : 0 < v := thetaRho_positive x
  have hX : X (thetaPoint v) = -|x| := by
    rw [thetaPoint_coordinate hv]
    dsimp [v,thetaRho]
    rw [log_exp]
    ring
  have he := n_X (thetaPoint_mem hv)
  rw [hX,thetaPoint_profile hv,thetaTwo_sigma₁ hv,thetaFour_sigma₂ hv] at he
  have hn : n (-|x|) = n x := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx,n_even]
    · rw [abs_of_neg hx,neg_neg]
  rw [hn] at he
  rw [he]
  unfold thetaDensity thetaNome
  change 2*v*(2*exp (-π*v/4)*sigma₁ (exp (-π*v)))^2*sigma₂ (exp (-π*v))^2 = _
  rw [mul_pow,mul_pow,← exp_nat_mul]
  rw [show (2:ℕ)*(-π*v/4) = -π*v/2 by norm_num; ring]
  ring

/--
Explicit bounded remainder in the actual sine-density logarithmic tail.

The stated quantitative bound `log (8/9:ℝ) ≤ log (n x)+π/2*exp (2*|x|)-2*|x| ∧ log (n
x)+π/2*exp (2*|x|)-2*|x| ≤ log (40:ℝ)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 2.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.n_theta`,
`«2610.05164v2».SineContinuum.thetaDensity_log_bounds` with the arguments shown in the proof.
-/
theorem n_log_bounds (x : ℝ) :
    log (8/9:ℝ) ≤ log (n x)+π/2*exp (2*|x|)-2*|x| ∧
      log (n x)+π/2*exp (2*|x|)-2*|x| ≤ log (40:ℝ) := by
  rw [n_theta]
  exact thetaDensity_log_bounds x

/--
The stated quantitative bound `(8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ n x ∧ n x ≤
40*(thetaRho x*exp (-π*thetaRho x/2))`.

Use: `«2610.05164v2».LocalObstruction.sine_amplitude_exp_decay` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun x => n
x*exp (a*x)) atTop (𝓝 0)`.

Article: 2610.05164v2, Proposition 2.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.n_theta`,
`«2610.05164v2».SineContinuum.thetaDensity_envelope` with the arguments shown in the proof.
-/
theorem n_theta_envelope (x : ℝ) :
    (8/9:ℝ)*(thetaRho x*exp (-π*thetaRho x/2)) ≤ n x ∧
      n x ≤ 40*(thetaRho x*exp (-π*thetaRho x/2)) := by
  rw [n_theta]
  exact thetaDensity_envelope x

end
end «2610.05164v2».SineContinuum
