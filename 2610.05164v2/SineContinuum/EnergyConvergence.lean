import «2610.05164v2».SineContinuum.EnergyThetaIntegral

/-!
Article: 2610.05164v2, Proposition 10.
Every finite theta-energy truncation converges to the actual theta integral.
Use: `«2610.05164v2».SineContinuum.thetaEnergy_truncations_tendsto` feeds
`«2610.05164v2».SineContinuum.energy_truncations_tendsto` (energy truncations tendsto).
Proof chain: `«2610.05164v2».SineContinuum.energyFiniteSum_tendsto` — 2610.05164v2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Convergence along the specified source filter to the specified limit: `Tendsto energyMoment
atTop (𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.energyRemainder_tendsto_zero` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto energyRemainder
atTop (𝓝 0)`.

Article: 2610.05164v2, Proposition 10 via
`«2610.05164v2».SineContinuum.energyFiniteSum_tendsto`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem energyMoment_tendsto_zero : Tendsto energyMoment atTop (𝓝 0) := by
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto (fun v : ℝ => v*π) atTop atTop := tendsto_id.atTop_mul_const pi_pos
  have he := tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hl)
  have hi := tendsto_inv_atTop_zero.comp hl
  have h := he.mul (hi.add ((hi.pow 2).const_mul 2) |>.add ((hi.pow 3).const_mul 2))
  convert h using 1
  · funext v
    dsimp [energyMoment]
    simp only [div_eq_mul_inv,inv_pow,neg_mul]
    ring
  · norm_num

/--
The full remainder of Lemma 7 tends to zero at the printed truncation orders.

Convergence along the specified source filter to the specified limit: `Tendsto energyRemainder
atTop (𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.thetaEnergy_truncations_tendsto` uses this limit to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun K
: ℕ => 512*∫ t in Set.Ioi (1:ℝ), partialEnergyIntegrand K t) atTop (𝓝 thetaEnergy)`.

Article: 2610.05164v2, Proposition 10 via
`«2610.05164v2».SineContinuum.energyFiniteSum_tendsto`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem energyRemainder_tendsto_zero : Tendsto energyRemainder atTop (𝓝 0) := by
  -- Record the convergence hn with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hn : Tendsto (fun K : ℕ => (K:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 := tendsto_atTop_add_const_right atTop (1:ℝ) hn
  have h2 := tendsto_atTop_add_const_right atTop (2:ℝ) hn
  -- Record the convergence ha with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ha : Tendsto (fun K : ℕ => (3/2:ℝ)+(K+1:ℕ)*(K+2:ℕ)) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (3/2:ℝ) (h1.atTop_mul_atTop₀ h2) using 1
    funext K; push_cast; ring
  -- Record the convergence hb with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hb : Tendsto (fun K : ℕ => (3/2:ℝ)+(K+1:ℕ)^2) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (3/2:ℝ) (h1.atTop_mul_atTop₀ h1) using 1
    funext K; push_cast; ring
  -- Record the convergence hda with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hda : Tendsto (fun K : ℕ => 2*(K+2:ℕ)*π) atTop atTop := by
    convert (h2.const_mul_atTop (by norm_num : (0:ℝ)<2)).atTop_mul_const pi_pos using 1
    funext K; push_cast; ring
  -- Record the convergence hdb with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hdb : Tendsto (fun K : ℕ => (2*K+3:ℕ)*π) atTop atTop := by
    convert (tendsto_atTop_add_const_right atTop (3:ℝ)
      (hn.const_mul_atTop (by norm_num : (0:ℝ)<2))).atTop_mul_const pi_pos using 1
    funext K; push_cast; ring
  have hEa := energyMoment_tendsto_zero.comp ha
  have hEb := energyMoment_tendsto_zero.comp hb
  have hDa := (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hda)).const_sub 1
  have hDb := (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdb)).const_sub 1
  have h := (((hEa.const_mul (6*energyM₁^5*energyM₂^6)).div hDa (by norm_num)).add
    ((hEb.const_mul (12*energyM₁^6*energyM₂^5)).div hDb (by norm_num))).const_mul 512
  convert h using 1
  · funext K
    dsimp [energyRemainder]
    simp only [neg_mul]
  · norm_num

/--
Every finite theta-energy truncation converges to the actual theta integral.

Convergence along the specified source filter to the specified limit: `Tendsto (fun K : ℕ =>
512*∫ t in Set.Ioi (1:ℝ), partialEnergyIntegrand K t) atTop (𝓝 thetaEnergy)`.

Use: `«2610.05164v2».SineContinuum.energy_truncations_tendsto` uses this limit to establish the
stated quantitative bound `Filter.Tendsto (fun K : ℕ => 512*∫ t in Ioi (1:ℝ),
partialEnergyIntegrand K t) Filter.atTop (nhds SineJacobi.energy)`.

Article: 2610.05164v2, Proposition 10 via
`«2610.05164v2».SineContinuum.energyFiniteSum_tendsto`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem thetaEnergy_truncations_tendsto :
    Tendsto (fun K : ℕ => 512*∫ t in Set.Ioi (1:ℝ), partialEnergyIntegrand K t)
      atTop (𝓝 thetaEnergy) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun K => norm_nonneg _)
    (fun K => by simpa only [Real.norm_eq_abs,abs_sub_comm] using thetaEnergy_error K)
    energyRemainder_tendsto_zero

end
end «2610.05164v2».SineContinuum
