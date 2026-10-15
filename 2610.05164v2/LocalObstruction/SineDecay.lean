import «2610.05164v2».SineContinuum.ThetaIdentity
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Article: 2610.05164v2, Theorem 6.1.
The actual sine amplitude is smaller than every exponential at +infinity, as required in (54) and
the final argument of Theorem 6.1.
Use: `«2610.05164v2».LocalObstruction.sine_amplitude_div_exponential` feeds
`«2610.05164v2».LocalObstruction.no_sine_stationary_identity` (no sine stationary identity).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Real Filter «2610.05164v2».SineContinuum
open scoped Topology

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun x => n
x*exp (a*x)) atTop (𝓝 0)`.

Use: `«2610.05164v2».LocalObstruction.sine_amplitude_div_exponential` uses this limit to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun x
=> n x/exp (-2*x)) atTop (𝓝 0)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem sine_amplitude_exp_decay (a : ℝ) :
    Tendsto (fun x => n x*exp (a*x)) atTop (𝓝 0) := by
  -- Record the convergence ht with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ht : Tendsto (fun x : ℝ => exp (2*x)/(2*x)) atTop atTop := by
    simpa only [Function.comp_def,pow_one,id_eq] using
      (tendsto_exp_div_pow_atTop 1).comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hb : ∀ᶠ x : ℝ in atTop, n x*exp (a*x) ≤ 40*exp (-x) := by
    filter_upwards [ht.eventually (eventually_gt_atTop ((a+3)/π)),
      eventually_gt_atTop (0:ℝ)] with x hx hx₀
    have h := (lt_div_iff₀ (by positivity : 0<2*x)).mp hx
    have hp := mul_lt_mul_of_pos_left h (div_pos pi_pos (by norm_num : (0:ℝ)<2))
    have he : π/2*exp (2*x) ≥ (a+3)*x := by
      have hc : π/2*((a+3)/π*(2*x))=(a+3)*x := by field_simp
      rw [hc] at hp
      exact hp.le
    have hn := (n_theta_envelope x).2
    dsimp only [thetaRho] at hn
    rw [abs_of_pos hx₀] at hn
    calc
      n x*exp (a*x) ≤ (40*(exp (2*x)*exp (-π*exp (2*x)/2)))*exp (a*x) :=
        mul_le_mul_of_nonneg_right hn (exp_pos _).le
      _ = 40*exp (-π/2*exp (2*x)+(a+2)*x) := by
        rw [← exp_add, mul_assoc, ← exp_add]
        congr 2
        ring
      _ ≤ 40*exp (-x) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        nlinarith
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto (fun x : ℝ => 40*exp (-x)) atTop (𝓝 0) := by
    simpa using (tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (40:ℝ)
  exact squeeze_zero' (Eventually.of_forall (fun x =>
    mul_nonneg (n_positive x).le (exp_pos _).le)) hb hl

/--
Convergence along the specified source filter to the specified limit: `Tendsto n atTop (𝓝 0)`.

Use: `«2610.05164v2».LocalObstruction.amplitude_correction_direction` uses this limit to
establish constructs witnesses with the exact properties `∃ w : SmoothTest, (∫ x, w x)=0 ∧ 0<(∫
x, n x*w x)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.sine_amplitude_exp_decay`
with the arguments shown in the proof.
-/
theorem sine_amplitude_tendsto_zero : Tendsto n atTop (𝓝 0) := by simpa using sine_amplitude_exp_decay 0

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun x => n
x/exp (-2*x)) atTop (𝓝 0)`.

Use: `«2610.05164v2».LocalObstruction.no_sine_stationary_identity` uses this limit to establish
exact identity `¬ ∀ᶠ x in atTop, (3/2:ℝ)*n x=α+ζ/(2*n x)+g x`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sine_amplitude_div_exponential :
    Tendsto (fun x => n x/exp (-2*x)) atTop (𝓝 0) := by
  convert sine_amplitude_exp_decay 2 using 1
  funext x
  rw [div_eq_mul_inv,← exp_neg]
  congr 2
  ring

end
end «2610.05164v2».LocalObstruction
