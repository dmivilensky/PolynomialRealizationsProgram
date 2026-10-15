import «2610.05164v2».SineContinuum.EnergyFiniteIntegral
import «2610.05164v2».SineContinuum.ThetaMajorants

/-!
Article: 2610.05164v2, Proposition 10.
The integrable two-exponential error majorant of Lemma 7.
Use: `«2610.05164v2».SineContinuum.energy_integrand_error` feeds
`«2610.05164v2».SineContinuum.thetaEnergy_error` (Lemma 7's full integration error for the theta
expression, at every order).
Proof chain: `«2610.05164v2».SineContinuum.energyFiniteSum_error` — 2610.05164v2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `exp (-π*t)^j = exp (-(j:ℝ)*π*t)`.

Use:
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.M₁_formula`
uses this identity to establish the identity `energyM₁ = 1/(1-exp (-π)^2)`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem nome_power (t : ℝ) (j : ℕ) :
    exp (-π*t)^j = exp (-(j:ℝ)*π*t) := by
  rw [← exp_nat_mul]
  congr 1
  ring

/--
The stated quantitative bound `0 ≤ exp (-π*t) ∧ exp (-π*t) ≤ exp (-π) ∧ exp (-π) < 1`.

Use:
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.energy_series_remainders`
uses this bound to establish the bound stated in that declaration.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
private theorem nome_range {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ exp (-π*t) ∧ exp (-π*t) ≤ exp (-π) ∧ exp (-π) < 1 :=
  ⟨(exp_pos _).le,exp_le_exp.mpr (by nlinarith [pi_pos]),exp_lt_one_iff.mpr (by linarith [pi_pos])⟩

/--
Exact identity `energyM₁ = 1/(1-exp (-π)^2)`.

Use: `«2610.05164v2».SineContinuum.energy_series_majorants` rewrites with this identity to
establish the stated quantitative bound `|sigma₁ (exp (-π*t))| ≤ energyM₁ ∧ |sigma₁Partial K
(exp (-π*t))| ≤ energyM₁ ∧ |sigma₂ (exp (-π*t))| ≤ energyM₂ ∧ |sigma₂Partial K (exp (-π*t))| ≤
energyM₂`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.nome_power`
with the arguments shown in the proof.
-/
private theorem M₁_formula : energyM₁ = 1/(1-exp (-π)^2) := by
  have h := nome_power 1 2
  norm_num only [mul_one,Nat.cast_ofNat] at h
  rw [h]
  rfl

/--
Exact identity `energyM₂ = 1+2*exp (-π)/(1-exp (-π)^3)`.

Use: `«2610.05164v2».SineContinuum.energy_series_majorants` rewrites with this identity to
establish the stated quantitative bound `|sigma₁ (exp (-π*t))| ≤ energyM₁ ∧ |sigma₁Partial K
(exp (-π*t))| ≤ energyM₁ ∧ |sigma₂ (exp (-π*t))| ≤ energyM₂ ∧ |sigma₂Partial K (exp (-π*t))| ≤
energyM₂`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.nome_power`
with the arguments shown in the proof.
-/
private theorem M₂_formula : energyM₂ = 1+2*exp (-π)/(1-exp (-π)^3) := by
  have h := nome_power 1 3
  norm_num only [mul_one,Nat.cast_ofNat] at h
  rw [h]
  rfl

/--
The stated quantitative bound `0 < energyM₁`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this bound to establish the
stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energyM₁_positive : 0 < energyM₁ := by
  unfold energyM₁
  exact one_div_pos.mpr (sub_pos.mpr (exp_lt_one_iff.mpr (by linarith [pi_pos])))

/--
The stated quantitative bound `0 < energyM₂`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this bound to establish the
stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energyM₂_positive : 0 < energyM₂ := by
  unfold energyM₂
  have hp : 0 < 1-exp (-3*π) := sub_pos.mpr (exp_lt_one_iff.mpr (by linarith [pi_pos]))
  positivity

/--
The full and truncated series obey exactly the constants of Lemma 7.

The stated quantitative bound `|sigma₁ (exp (-π*t))| ≤ energyM₁ ∧ |sigma₁Partial K (exp
(-π*t))| ≤ energyM₁ ∧ |sigma₂ (exp (-π*t))| ≤ energyM₂ ∧ |sigma₂Partial K (exp (-π*t))| ≤
energyM₂`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this bound to establish the
stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.nome_range`,
`«2610.05164v2».SineContinuum.sigma₁_majorants`,
`«2610.05164v2».SineContinuum.sigma₂_majorants` with the arguments shown in the proof.
-/
theorem energy_series_majorants {t : ℝ} (ht : 1 ≤ t) (K : ℕ) :
    |sigma₁ (exp (-π*t))| ≤ energyM₁ ∧ |sigma₁Partial K (exp (-π*t))| ≤ energyM₁ ∧
    |sigma₂ (exp (-π*t))| ≤ energyM₂ ∧ |sigma₂Partial K (exp (-π*t))| ≤ energyM₂ := by
  -- Apply
  -- `_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.nome_range`,
  -- `«2610.05164v2».SineContinuum.sigma₁_majorants`,
  -- `«2610.05164v2».SineContinuum.sigma₂_majorants` to the displayed hypotheses, then match
  -- the resulting expression to the goal.
  obtain ⟨hq,hqq,h₀⟩ := nome_range ht
  obtain ⟨hp,hpb,hf,hfb⟩ := sigma₁_majorants hq hqq h₀ K
  obtain ⟨h₂p,h₂f⟩ := sigma₂_majorants hq hqq h₀ K
  rw [M₁_formula,M₂_formula]
  exact ⟨by rwa [abs_of_nonneg hf],by rwa [abs_of_nonneg hp],h₂f,h₂p⟩

/--
The stated quantitative bound `0 < 1-exp (-2*(K+2:ℕ)*π)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 10.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem denominator₁_positive (K : ℕ) :
    0 < 1-exp (-2*(K+2:ℕ)*π) := by
  apply sub_pos.mpr
  rw [exp_lt_one_iff]
  have hk : (0:ℝ) < (K+2:ℕ) := by positivity
  nlinarith [pi_pos]

/--
The stated quantitative bound `0 < 1-exp (-(2*K+3:ℕ)*π)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 10.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem denominator₂_positive (K : ℕ) :
    0 < 1-exp (-(2*K+3:ℕ)*π) := by
  apply sub_pos.mpr
  rw [exp_lt_one_iff]
  have hk : (0:ℝ) < (2*K+3:ℕ) := by positivity
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) pi_pos

/--
The stated quantitative bound `|sigma₁ (exp (-π*t))-sigma₁Partial K (exp (-π*t))| ≤ exp
(-π*t)^((K+1)*(K+2))/(1-exp (-2*(K+2:ℕ)*π)) ∧ |sigma₂ (exp (-π*t))-sigma₂Partial K (exp
(-π*t))| ≤ 2*exp (-π*t)^((K+1)^2)/(1-exp (-(2*K+3:ℕ)*π))`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this bound to establish the
stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.nome_range`,
`«2610.05164v2».SineContinuum.theta_remainder_bounds` with the arguments shown in the proof.
-/
private theorem energy_series_remainders {t : ℝ} (ht : 1 ≤ t) (K : ℕ) :
    |sigma₁ (exp (-π*t))-sigma₁Partial K (exp (-π*t))| ≤
      exp (-π*t)^((K+1)*(K+2))/(1-exp (-2*(K+2:ℕ)*π)) ∧
    |sigma₂ (exp (-π*t))-sigma₂Partial K (exp (-π*t))| ≤
      2*exp (-π*t)^((K+1)^2)/(1-exp (-(2*K+3:ℕ)*π)) := by
  -- Apply
  -- `_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.nome_range`,
  -- `«2610.05164v2».SineContinuum.theta_remainder_bounds` to the displayed hypotheses, then
  -- match the resulting expression to the goal.
  obtain ⟨hq,hqq,h₀⟩ := nome_range ht
  have h := theta_remainder_bounds hq hqq h₀ K
  have ha : exp (-π)^(2*(K+2)) = exp (-2*(K+2:ℕ)*π) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have hb : exp (-π)^(2*K+3) = exp (-(2*K+3:ℕ)*π) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  rwa [ha,hb] at h

/--
Defines `thetaEnergyIntegrand` of type `ℝ` by `t^2*exp (-(3/2)*π*t)*sigma₁ (exp
(-π*t))^6*sigma₂ (exp (-π*t))^6`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this definition to establish
the stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energy_eq_thetaEnergy`.
-/
def thetaEnergyIntegrand (t : ℝ) : ℝ :=
  t^2*exp (-(3/2)*π*t)*sigma₁ (exp (-π*t))^6*sigma₂ (exp (-π*t))^6

/--
Defines `partialEnergyIntegrand` of type `ℝ` by `t^2*exp (-(3/2)*π*t)*sigma₁Partial K (exp
(-π*t))^6*sigma₂Partial K (exp (-π*t))^6`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this definition to establish
the stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via
`«2610.05164v2».SineContinuum.energyFiniteSum_integral`.
-/
def partialEnergyIntegrand (K : ℕ) (t : ℝ) : ℝ :=
  t^2*exp (-(3/2)*π*t)*sigma₁Partial K (exp (-π*t))^6*sigma₂Partial K (exp (-π*t))^6

/--
Defines `energyErrorMajorant` of type `ℝ` by `(6*energyM₁^5*energyM₂^6/(1-exp (-2*(K+2:ℕ)*π)))*
(t^2*exp (-(3/2+(K+1:ℕ)*(K+2:ℕ))*π*t)) + (12*energyM₁^6*energyM₂^5/(1-exp (-(2*K+3:ℕ)*π)))*
(t^2*exp (-(3/2+(K+1:ℕ)^2)*π*t))`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` uses this definition to establish
the stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.
-/
def energyErrorMajorant (K : ℕ) (t : ℝ) : ℝ :=
  (6*energyM₁^5*energyM₂^6/(1-exp (-2*(K+2:ℕ)*π)))*
    (t^2*exp (-(3/2+(K+1:ℕ)*(K+2:ℕ))*π*t)) +
  (12*energyM₁^6*energyM₂^5/(1-exp (-(2*K+3:ℕ)*π)))*
    (t^2*exp (-(3/2+(K+1:ℕ)^2)*π*t))

/--
Exact identity `(t^2*exp (-(3/2)*π*t))*exp (-π*t)^j = t^2*exp (-(3/2+(j:ℝ))*π*t)`.

Use: `«2610.05164v2».SineContinuum.energy_integrand_error` rewrites with this identity to
establish the stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.nome_power`
with the arguments shown in the proof.
-/
private theorem weighted_nome (t : ℝ) (j : ℕ) :
    (t^2*exp (-(3/2)*π*t))*exp (-π*t)^j = t^2*exp (-(3/2+(j:ℝ))*π*t) := by
  rw [nome_power,mul_assoc,← exp_add]
  congr 1
  congr 1
  ring

/--
The integrable two-exponential error majorant of Lemma 7.

The stated quantitative bound `|thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤
energyErrorMajorant K t`.

Use: `«2610.05164v2».SineContinuum.thetaEnergy_error` uses this bound to establish the stated
quantitative bound `|thetaEnergy-512*(∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t)| ≤
energyRemainder K`.

Article: 2610.05164v2, Proposition 10 via `«2610.05164v2».SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.energy_series_majorants`,
`_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.energy_series_remainders`,
`«2610.05164v2».SineContinuum.energyM₁_positive` with the arguments shown in the proof.
-/
theorem energy_integrand_error {t : ℝ} (ht : 1 ≤ t) (K : ℕ) :
    |thetaEnergyIntegrand t-partialEnergyIntegrand K t| ≤ energyErrorMajorant K t := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.energy_series_majorants`,
  -- `_private.«2610.05164v2».SineContinuum.EnergyRemainder.0.«2610.05164v2».SineContinuum.energy_series_remainders`,
  -- `«2610.05164v2».SineContinuum.energyM₁_positive` with the arguments shown in the proof.
  obtain ⟨hX,hx,hY,hy⟩ := energy_series_majorants ht K
  obtain ⟨ha,hb⟩ := energy_series_remainders ht K
  have hA : 0 ≤ 6*energyM₁^5*energyM₂^6 := by positivity [energyM₁_positive,energyM₂_positive]
  have hB : 0 ≤ 6*energyM₁^6*energyM₂^5 := by positivity [energyM₁_positive,energyM₂_positive]
  have hd := sixth_product_difference hX hx hY hy
  have hh := hd.trans (add_le_add (mul_le_mul_of_nonneg_left ha hA) (mul_le_mul_of_nonneg_left hb hB))
  have h := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg t) (exp_pos (-(3/2)*π*t)).le)
  have he : (t^2*exp (-(3/2)*π*t))*
      (6*energyM₁^5*energyM₂^6*(exp (-π*t)^((K+1)*(K+2))/(1-exp (-2*(K+2:ℕ)*π)))+
      6*energyM₁^6*energyM₂^5*(2*exp (-π*t)^((K+1)^2)/(1-exp (-(2*K+3:ℕ)*π)))) =
        energyErrorMajorant K t := by
    unfold energyErrorMajorant
    rw [show (3/2+(K+1:ℕ)*(K+2:ℕ):ℝ) = 3/2+(((K+1)*(K+2):ℕ):ℝ) by push_cast; ring,
      ← weighted_nome t ((K+1)*(K+2)),
      show (3/2+(K+1:ℕ)^2:ℝ) = 3/2+(((K+1)^2:ℕ):ℝ) by push_cast; ring,
      ← weighted_nome t ((K+1)^2)]
    ring
  rw [he] at h
  convert h using 1
  rw [← abs_of_nonneg (mul_nonneg (sq_nonneg t) (exp_pos (-(3/2)*π*t)).le),← abs_mul]
  congr 1
  unfold thetaEnergyIntegrand partialEnergyIntegrand
  ring

end
end «2610.05164v2».SineContinuum
