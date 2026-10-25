import chebyshev2.SineContinuum.ThetaIdentity
import chebyshev2.SineContinuum.EnergyConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Article: chebyshev2, Proposition 10.
Lemma 7 for the article's c_sin, at every finite order.
Use: `chebyshev2.SineContinuum.energy_truncations_tendsto` feeds
`chebyshev2.SineContinuum.energyFiniteSum_tendsto` (energy Finite Sum tendsto).
Proof chain: `chebyshev2.SineContinuum.energyFiniteSum_tendsto` — chebyshev2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(fun v : ℝ => (1/2)*log v) '' Ioi (1:ℝ) = Ioi (0:ℝ)`.

Use: `chebyshev2.SineContinuum.energy_eq_thetaEnergy` rewrites with this identity to
establish exact identity `SineJacobi.energy = thetaEnergy`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energy_eq_thetaEnergy`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem logTime_image : (fun v : ℝ => (1/2)*log v) '' Ioi (1:ℝ) = Ioi (0:ℝ) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact mul_pos (by norm_num) (log_pos hv)
  · intro hx
    refine ⟨exp (2*x),?_,?_⟩
    · exact one_lt_exp_iff.mpr (by change 0<x at hx; linarith)
    · dsimp only; rw [log_exp]; ring

/--
Exact identity `n ((1/2)*log v) = 8*v*exp (-π*v/2)*sigma₁ (exp (-π*v))^2*sigma₂ (exp
(-π*v))^2`.

Use: `chebyshev2.SineContinuum.energy_eq_thetaEnergy` rewrites with this identity to
establish exact identity `SineJacobi.energy = thetaEnergy`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energy_eq_thetaEnergy`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_theta` with the arguments
shown in the proof.
-/
private theorem n_logTime {v : ℝ} (hv : 1 < v) :
    n ((1/2)*log v) = 8*v*exp (-π*v/2)*sigma₁ (exp (-π*v))^2*sigma₂ (exp (-π*v))^2 := by
  rw [n_theta]
  unfold thetaDensity thetaNome thetaRho
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (log_nonneg hv.le)),
    show 2*((1/2:ℝ)*log v) = log v by ring,exp_log (by linarith : 0<v)]

/--
Equation (26): the sine energy is the actual theta integral of Lemma 7.

Exact identity `SineJacobi.energy = thetaEnergy`.

Use: `chebyshev2.SineContinuum.energy_error` rewrites with this identity to establish the
stated quantitative bound `|SineJacobi.energy-512*(∫ t in Ioi (1:ℝ), partialEnergyIntegrand K
t)| ≤ energyRemainder K`.

Article: chebyshev2, Proposition 10.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Identify the summands/integrands on their required domain before replacing
the sum or integral. Clear the denominators using the available nonzero hypotheses, then verify
the remaining algebraic identity.
-/
theorem energy_eq_thetaEnergy : SineJacobi.energy = thetaEnergy := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have ha : (fun x : ℝ => n |x|^3) = (fun x => n x^3) := by
    funext x
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx,n_even]
  have hh := integral_comp_abs (f:=fun x : ℝ => n x^3)
  rw [ha] at hh
  have hj := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s:=Ioi (1:ℝ)) (f:=fun v => (1/2)*log v) (f':=fun v => (1/2)*v⁻¹)
    measurableSet_Ioi
    (fun v hv => ((hasDerivAt_log (by have hv' : 1<v := hv; linarith : v ≠ 0)).const_mul (1/2)).hasDerivWithinAt)
    (fun a ha b hb hab => mul_le_mul_of_nonneg_left
      (log_le_log (by have ha' : 1<a := ha; linarith : 0<a) hab) (by norm_num)) (fun x => n x^3)
  rw [logTime_image] at hj
  have he : (∫ x : ℝ, n x^3) = SineJacobi.energy := by
    calc
      _ = ∫ x : ℝ, m x*sqrt (m x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [sqrt_m,m]; ring)
      _ = _ := energy
  rw [← he,hh,hj]
  have hi : (∫ v in Ioi (1:ℝ), ((1/2)*v⁻¹) • n ((1/2)*log v)^3) =
      ∫ v in Ioi (1:ℝ), 256*thetaEnergyIntegrand v := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    change 1<v at hv
    rw [n_logTime hv,smul_eq_mul]
    unfold thetaEnergyIntegrand
    rw [mul_pow,mul_pow,mul_pow,mul_pow,← exp_nat_mul]
    rw [show (3:ℕ)*(-π*v/2) = -(3/2)*π*v by norm_num; ring]
    field_simp [show v ≠ 0 by linarith [hv]]
    ring
  rw [hi,integral_const_mul,thetaEnergy]
  ring

/--
Lemma 7 for the article's c_sin, at every finite order.

The stated quantitative bound `|SineJacobi.energy-512*(∫ t in Ioi (1:ℝ), partialEnergyIntegrand
K t)| ≤ energyRemainder K`.

Use: `chebyshev2.SineContinuum.energyFiniteSum_error` uses this bound to establish the
stated quantitative bound `|SineJacobi.energy-energyFiniteSum K| ≤ energyRemainder K`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energy_eq_thetaEnergy`,
`chebyshev2.SineContinuum.thetaEnergy_error` with the arguments shown in the proof.
-/
theorem energy_error (K : ℕ) :
    |SineJacobi.energy-512*(∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t)| ≤ energyRemainder K := by
  rw [energy_eq_thetaEnergy]
  exact thetaEnergy_error K

/--
The stated quantitative bound `|SineJacobi.energy-energy3| ≤ energyRemainder 3`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 10.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energy_eq_thetaEnergy`,
`chebyshev2.SineContinuum.thetaEnergy_error3` with the arguments shown in the proof.
-/
theorem energy_error3 : |SineJacobi.energy-energy3| ≤ energyRemainder 3 := by
  rw [energy_eq_thetaEnergy]
  exact thetaEnergy_error3

/--
The stated quantitative bound `Filter.Tendsto (fun K : ℕ => 512*∫ t in Ioi (1:ℝ),
partialEnergyIntegrand K t) Filter.atTop (nhds SineJacobi.energy)`.

Use: `chebyshev2.SineContinuum.energyFiniteSum_tendsto` uses this identity to establish the
precise assertion is `Filter.Tendsto energyFiniteSum Filter.atTop (nhds SineJacobi.energy)`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_tendsto`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energy_eq_thetaEnergy`,
`chebyshev2.SineContinuum.thetaEnergy_truncations_tendsto` with the arguments shown in the
proof.
-/
theorem energy_truncations_tendsto :
    Filter.Tendsto (fun K : ℕ => 512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t)
      Filter.atTop (nhds SineJacobi.energy) := by
  rw [energy_eq_thetaEnergy]
  exact thetaEnergy_truncations_tendsto

end
end chebyshev2.SineContinuum
