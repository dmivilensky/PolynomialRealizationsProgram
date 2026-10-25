import chebyshev2.SineContinuum.ThetaBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Article: chebyshev2, Proposition 10.
The elementary decay bound used at the end of Lemma 7.
Use: `chebyshev2.SineContinuum.energyMoment_integral` feeds
`chebyshev2.SineContinuum.finiteEnergyIntegrand_integral` (Integration of the finite polynomial
gives exactly the sum of Lemma 7).
Proof chain: `chebyshev2.SineContinuum.energyFiniteSum_integral` — chebyshev2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology Real
set_option backward.isDefEq.respectTransparency true

/--
The closed form of I(lambda) in Lemma 7.

Use: `chebyshev2.SineContinuum.energyMoment_integral` rewrites with this definition to
establish exact identity `(∫ t : ℝ in Ioi 1, t^2*exp (-v*π*t)) = energyMoment v`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.
-/
def energyMoment (v : ℝ) : ℝ :=
  exp (-v*π)*(1/(v*π)+2/(v*π)^2+2/(v*π)^3)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun t : ℝ =>
t^j*exp (-c*t)) atTop (𝓝 0)`.

Use:
`_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_limit`
uses this limit to establish convergence along the specified source filter to the specified
limit: `Tendsto (momentPrimitive c) atTop (𝓝 0)`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
private theorem polynomial_exp_limit {c : ℝ} (hc : 0 < c) (j : ℕ) :
    Tendsto (fun t : ℝ => t^j*exp (-c*t)) atTop (𝓝 0) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
    (tendsto_id.const_mul_atTop hc)).div_const (c^j)
  convert h using 1
  · funext t
    dsimp
    rw [mul_pow]
    field_simp [hc.ne']
  · simp

/--
Defines `momentPrimitive` of type `ℝ` by `-(t^2*exp (-c*t)/c+2*(t*exp (-c*t))/c^2+2*exp
(-c*t)/c^3)`.

Use:
`_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_limit`
uses this definition to establish convergence along the specified source filter to the
specified limit: `Tendsto (momentPrimitive c) atTop (𝓝 0)`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.
-/
private def momentPrimitive (c t : ℝ) : ℝ :=
  -(t^2*exp (-c*t)/c+2*(t*exp (-c*t))/c^2+2*exp (-c*t)/c^3)

/--
The actual derivative at the stated point: `HasDerivAt (momentPrimitive c) (t^2*exp (-c*t)) t`.

Use: `chebyshev2.SineContinuum.energyMoment_integrable` uses this derivative formula to
establish integrability on the stated domain: `IntegrableOn (fun t : ℝ => t^2*exp (-v*π*t))
(Ioi 1)`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem momentPrimitive_derivative {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (momentPrimitive c) (t^2*exp (-c*t)) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he := ((hasDerivAt_id t).const_mul (-c)).exp
  have h := ((((hasDerivAt_id t).pow 2).mul he).div_const c |>.add
    (((hasDerivAt_id t).mul he).const_mul 2 |>.div_const (c^2)) |>.add
    (he.const_mul 2 |>.div_const (c^3))).neg
  convert h using 1
  · rfl
  · dsimp
    field_simp
    ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto (momentPrimitive
c) atTop (𝓝 0)`.

Use: `chebyshev2.SineContinuum.energyMoment_integrable` uses this limit to establish
integrability on the stated domain: `IntegrableOn (fun t : ℝ => t^2*exp (-v*π*t)) (Ioi 1)`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.polynomial_exp_limit`
with the arguments shown in the proof.
-/
private theorem momentPrimitive_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (momentPrimitive c) atTop (𝓝 0) := by
  have h := (((polynomial_exp_limit hc 2).div_const c).add
    ((polynomial_exp_limit hc 1).const_mul 2 |>.div_const (c^2)) |>.add
    ((polynomial_exp_limit hc 0).const_mul 2 |>.div_const (c^3))).neg
  unfold momentPrimitive
  simpa only [zero_div,mul_zero,add_zero,neg_zero,pow_one,pow_zero,one_mul,
    ] using h

/--
Integrability on the exact semi-infinite integration domain of Lemma 7.

Integrability on the stated domain: `IntegrableOn (fun t : ℝ => t^2*exp (-v*π*t)) (Ioi 1)`.

Use:
`_private.chebyshev2.SineContinuum.EnergyThetaIntegral.0.chebyshev2.SineContinuum.weighted_integrable`
uses this integrability result to establish integrability on the stated domain: `IntegrableOn
(fun t : ℝ => (t^2*exp (-(3/2)*π*t))*f t) (Ioi 1)`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_derivative`,
`_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_limit`
with the arguments shown in the proof.
-/
theorem energyMoment_integrable {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun t : ℝ => t^2*exp (-v*π*t)) (Ioi 1) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => by simpa only [neg_mul] using momentPrimitive_derivative (mul_pos hv pi_pos).ne' t)
    (fun t _ => mul_nonneg (sq_nonneg t) (exp_pos _).le)
    (momentPrimitive_limit (mul_pos hv pi_pos))
/--
The actual improper integral, not an assumed quadrature formula.

Exact identity `(∫ t : ℝ in Ioi 1, t^2*exp (-v*π*t)) = energyMoment v`.

Use: `chebyshev2.SineContinuum.energyErrorMajorant_integral` rewrites with this identity to
establish exact identity `512*(∫ t in Ioi (1:ℝ), energyErrorMajorant K t) = energyRemainder K`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_derivative`,
`_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_limit`
with the arguments shown in the proof.
-/
theorem energyMoment_integral {v : ℝ} (hv : 0 < v) :
    (∫ t : ℝ in Ioi 1, t^2*exp (-v*π*t)) = energyMoment v := by
  -- Use the identities/estimates
  -- `_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_derivative`,
  -- `_private.chebyshev2.SineContinuum.EnergyMoments.0.chebyshev2.SineContinuum.momentPrimitive_limit`
  -- with the arguments shown in the proof.
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t (_ : t ∈ Ici (1:ℝ)) => by simpa only [neg_mul] using momentPrimitive_derivative (mul_pos hv pi_pos).ne' t)
    (fun t (_ : t ∈ Ioi (1:ℝ)) => mul_nonneg (sq_nonneg t) (exp_pos _).le)
    (momentPrimitive_limit (mul_pos hv pi_pos))
  simp only [neg_mul]
  rw [h]
  simp only [momentPrimitive,energyMoment,zero_sub,neg_neg,one_pow,mul_one,neg_mul]
  ring

/--
The stated quantitative bound `0 < energyMoment v`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 10.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energyMoment_positive {v : ℝ} (hv : 0 < v) : 0 < energyMoment v := by
  unfold energyMoment
  positivity

/--
The elementary decay bound used at the end of Lemma 7.

The stated quantitative bound `energyMoment v ≤ exp (-v*π)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 10.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energyMoment_le_exp {v : ℝ} (hv : 1 ≤ v) :
    energyMoment v ≤ exp (-v*π) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hp : 3 < v*π := by nlinarith [pi_gt_three]
  have h₁ : 1/(v*π) ≤ (1/3:ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hp.le
  have h₂ : 2/(v*π)^2 ≤ (2/9:ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have h₃ : 2/(v*π)^3 ≤ (2/27:ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hp.le 3]
  unfold energyMoment
  calc
    _ ≤ exp (-v*π)*1 := mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
    _ = _ := mul_one _

end
end chebyshev2.SineContinuum
