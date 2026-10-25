import chebyshev2.SineContinuum.EnergyRemainder

/-!
Article: chebyshev2, Proposition 10.
Lemma 7's full integration error for the theta expression, at every order.
Use: `chebyshev2.SineContinuum.thetaEnergy_error` feeds
`chebyshev2.SineContinuum.thetaEnergy_error3` (theta Energy error3).
Proof chain: `chebyshev2.SineContinuum.energyFiniteSum_error` — chebyshev2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real Set MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false

/--
Measurability of the displayed map: `Measurable sigma₁`.

Use: `chebyshev2.SineContinuum.thetaEnergyIntegrand_integrable` uses this measurability
result to establish integrability on the stated domain: `IntegrableOn thetaEnergyIntegrand (Ioi
(1:ℝ))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
@[fun_prop] theorem sigma₁_measurable : Measurable sigma₁ :=
  Measurable.tsum (fun j => measurable_id.pow_const (j*(j+1)))

/--
Measurability of the displayed map: `Measurable sigma₂`.

Use: `chebyshev2.SineContinuum.thetaEnergyIntegrand_integrable` uses this measurability
result to establish integrability on the stated domain: `IntegrableOn thetaEnergyIntegrand (Ioi
(1:ℝ))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[fun_prop] theorem sigma₂_measurable : Measurable sigma₂ := by
  unfold sigma₂
  exact measurable_const.add (measurable_const.mul
    (Measurable.tsum (fun j => measurable_const.mul (measurable_id.pow_const ((j+1)^2)))))

/--
Measurability of the displayed map: `Measurable (sigma₁Partial K)`.

Use: `chebyshev2.SineContinuum.partialEnergyIntegrand_integrable` uses this measurability
result to establish integrability on the stated domain: `IntegrableOn (partialEnergyIntegrand
K) (Ioi (1:ℝ))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[fun_prop] theorem sigma₁Partial_measurable (K : ℕ) : Measurable (sigma₁Partial K) := by
  unfold sigma₁Partial
  fun_prop

/--
Measurability of the displayed map: `Measurable (sigma₂Partial K)`.

Use: `chebyshev2.SineContinuum.partialEnergyIntegrand_integrable` uses this measurability
result to establish integrability on the stated domain: `IntegrableOn (partialEnergyIntegrand
K) (Ioi (1:ℝ))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[fun_prop] theorem sigma₂Partial_measurable (K : ℕ) : Measurable (sigma₂Partial K) := by
  unfold sigma₂Partial
  fun_prop

/--
Integrability on the stated domain: `IntegrableOn (fun t : ℝ => (t^2*exp (-(3/2)*π*t))*f t)
(Ioi 1)`.

Use: `chebyshev2.SineContinuum.partialEnergyIntegrand_integrable` uses this integrability
result to establish integrability on the stated domain: `IntegrableOn (partialEnergyIntegrand
K) (Ioi (1:ℝ))`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
private theorem weighted_integrable {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t ∈ Ioi (1:ℝ), |f t| ≤ energyM₁^6*energyM₂^6) :
    IntegrableOn (fun t : ℝ => (t^2*exp (-(3/2)*π*t))*f t) (Ioi 1) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply ((energyMoment_integrable (v := 3/2) (by norm_num)).const_mul
    (energyM₁^6*energyM₂^6)).mono'
  · exact ((measurable_id.pow_const 2).mul (by fun_prop) |>.mul hf).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg (sq_nonneg t) (exp_pos _).le)]
    calc
      _ ≤ (t^2*exp (-(3/2)*π*t))*(energyM₁^6*energyM₂^6) :=
        mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
      _ = _ := by ring

/--
Integrability on the stated domain: `IntegrableOn thetaEnergyIntegrand (Ioi (1:ℝ))`.

Use: `chebyshev2.SineContinuum.thetaEnergy_error` rewrites with this integrability result
to prove the bound `|thetaEnergy-512*(∫ t in Ioi (1:ℝ),
partialEnergyIntegrand K t)| ≤ energyRemainder K`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.EnergyThetaIntegral.0.chebyshev2.SineContinuum.weighted_integrable`,
`chebyshev2.SineContinuum.energy_series_majorants` with the arguments shown in the proof.
-/
theorem thetaEnergyIntegrand_integrable : IntegrableOn thetaEnergyIntegrand (Ioi (1:ℝ)) := by
  -- Use the identities/estimates
  -- `_private.chebyshev2.SineContinuum.EnergyThetaIntegral.0.chebyshev2.SineContinuum.weighted_integrable`,
  -- `chebyshev2.SineContinuum.energy_series_majorants` with the arguments shown in the
  -- proof.
  have h := weighted_integrable (f := fun t => sigma₁ (exp (-π*t))^6*sigma₂ (exp (-π*t))^6)
    (by fun_prop) (by
      intro t ht
      obtain ⟨hX,_,hY,_⟩ := energy_series_majorants ht.le 0
      rw [abs_mul,abs_pow,abs_pow]
      gcongr)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  unfold thetaEnergyIntegrand
  ring

/--
Integrability on the stated domain: `IntegrableOn (partialEnergyIntegrand K) (Ioi (1:ℝ))`.

Use: `chebyshev2.SineContinuum.thetaEnergy_error` rewrites with this integrability result
to prove the bound `|thetaEnergy-512*(∫ t in Ioi (1:ℝ),
partialEnergyIntegrand K t)| ≤ energyRemainder K`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.EnergyThetaIntegral.0.chebyshev2.SineContinuum.weighted_integrable`,
`chebyshev2.SineContinuum.energy_series_majorants` with the arguments shown in the proof.
-/
theorem partialEnergyIntegrand_integrable (K : ℕ) :
    IntegrableOn (partialEnergyIntegrand K) (Ioi (1:ℝ)) := by
  -- Use the identities/estimates
  -- `_private.chebyshev2.SineContinuum.EnergyThetaIntegral.0.chebyshev2.SineContinuum.weighted_integrable`,
  -- `chebyshev2.SineContinuum.energy_series_majorants` with the arguments shown in the
  -- proof.
  have h := weighted_integrable (f := fun t => sigma₁Partial K (exp (-π*t))^6*sigma₂Partial K (exp (-π*t))^6)
    (by fun_prop) (by
      intro t ht
      obtain ⟨_,hx,_,hy⟩ := energy_series_majorants ht.le K
      rw [abs_mul,abs_pow,abs_pow]
      gcongr)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  unfold partialEnergyIntegrand
  ring

/--
Integrability on the stated domain: `IntegrableOn (energyErrorMajorant K) (Ioi (1:ℝ))`.

Use: `chebyshev2.SineContinuum.thetaEnergy_error` uses this integrability result to
establish the stated quantitative bound `|thetaEnergy-512*(∫ t in Ioi (1:ℝ),
partialEnergyIntegrand K t)| ≤ energyRemainder K`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energyMoment_integrable` with
the arguments shown in the proof.
-/
theorem energyErrorMajorant_integrable (K : ℕ) :
    IntegrableOn (energyErrorMajorant K) (Ioi (1:ℝ)) :=
  ((energyMoment_integrable (v := 3/2+(K+1:ℕ)*(K+2:ℕ)) (by positivity)).const_mul _).add
    ((energyMoment_integrable (v := 3/2+(K+1:ℕ)^2) (by positivity)).const_mul _)
/--
Exact identity `512*(∫ t in Ioi (1:ℝ), energyErrorMajorant K t) = energyRemainder K`.

Use: `chebyshev2.SineContinuum.thetaEnergy_error` uses this identity to establish the
stated quantitative bound `|thetaEnergy-512*(∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t)| ≤
energyRemainder K`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energyMoment_integrable`,
`chebyshev2.SineContinuum.energyMoment_integral` with the arguments shown in the proof.
-/
theorem energyErrorMajorant_integral (K : ℕ) :
    512*(∫ t in Ioi (1:ℝ), energyErrorMajorant K t) = energyRemainder K := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.energyMoment_integrable`,
  -- `chebyshev2.SineContinuum.energyMoment_integral` with the arguments shown in the
  -- proof.
  unfold energyErrorMajorant
  rw [integral_add
    ((energyMoment_integrable (v := 3/2+(K+1:ℕ)*(K+2:ℕ)) (by positivity)).const_mul _)
    ((energyMoment_integrable (v := 3/2+(K+1:ℕ)^2) (by positivity)).const_mul _),
    integral_const_mul,integral_const_mul,energyMoment_integral (by positivity),
    energyMoment_integral (by positivity)]
  unfold energyRemainder
  ring

/--
The actual theta-series energy integral, identified with the original c_sin by
`energy_eq_thetaEnergy` in `EnergyArticle`.

Use: `chebyshev2.SineContinuum.thetaEnergy_error` rewrites with this definition to
establish the stated quantitative bound `|thetaEnergy-512*(∫ t in Ioi (1:ℝ),
partialEnergyIntegrand K t)| ≤ energyRemainder K`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energy_eq_thetaEnergy`.
-/
def thetaEnergy : ℝ := 512*∫ t in Ioi (1:ℝ), thetaEnergyIntegrand t

/--
Lemma 7's full integration error for the theta expression, at every order.

The stated quantitative bound `|thetaEnergy-512*(∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t)|
≤ energyRemainder K`.

Use: `chebyshev2.SineContinuum.thetaEnergy_error3` uses this bound to establish the stated
quantitative bound `|thetaEnergy-energy3| ≤ energyRemainder 3`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem thetaEnergy_error (K : ℕ) :
    |thetaEnergy-512*(∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t)| ≤ energyRemainder K := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rw [thetaEnergy,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<512),
    ← integral_sub thetaEnergyIntegrand_integrable (partialEnergyIntegrand_integrable K)]
  calc
    _ ≤ 512*(∫ t in Ioi (1:ℝ), |thetaEnergyIntegrand t-partialEnergyIntegrand K t|) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (f := fun t : ℝ => thetaEnergyIntegrand t-partialEnergyIntegrand K t)
          (μ := volume.restrict (Ioi 1))
    _ ≤ 512*(∫ t in Ioi (1:ℝ), energyErrorMajorant K t) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply integral_mono_ae
        (thetaEnergyIntegrand_integrable.sub (partialEnergyIntegrand_integrable K)).abs
        (energyErrorMajorant_integrable K)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact energy_integrand_error ht.le K
    _ = _ := energyErrorMajorant_integral K

/--
The stated quantitative bound `|thetaEnergy-energy3| ≤ energyRemainder 3`.

Use: `chebyshev2.SineContinuum.energy_error3` uses this bound to establish the stated
quantitative bound `|SineJacobi.energy-energy3| ≤ energyRemainder 3`.

Article: chebyshev2, Proposition 10.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energy3_finite_integral`,
`chebyshev2.SineContinuum.thetaEnergy_error` with the arguments shown in the proof.
-/
theorem thetaEnergy_error3 : |thetaEnergy-energy3| ≤ energyRemainder 3 := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.energy3_finite_integral`,
  -- `chebyshev2.SineContinuum.thetaEnergy_error` with the arguments shown in the proof.
  have he : energy3 = 512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand 3 t := by
    rw [energy3_finite_integral]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    unfold partialEnergyIntegrand
    rw [show -(3/2:ℝ)*π*t = -3*π*t/2 by ring]
  rw [he]
  exact thetaEnergy_error 3


end
end chebyshev2.SineContinuum
