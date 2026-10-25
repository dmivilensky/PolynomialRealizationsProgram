import chebyshev2.SineContinuum.EnergyPolynomial
import chebyshev2.SineContinuum.ThetaTruncation

/-!
Article: chebyshev2, Lemma 7.
E_3 integrates the article's actual truncated series, not an unrelated approximation.
Use: `chebyshev2.SineContinuum.energy3_finite_integral` feeds
`chebyshev2.SineContinuum.energyFiniteSum_three` (The arbitrary-order finite sum specializes to
the certified E_3).
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real Set MeasureTheory Polynomial
set_option backward.isDefEq.respectTransparency false

/--
Real evaluation of the exact integer coefficient list.

Use:
`_private.chebyshev2.SineContinuum.EnergyFiniteIntegral.0.chebyshev2.SineContinuum.finiteEnergyIntegrand_cons`
rewrites with this definition to establish the identity `finiteEnergyIntegrand (c::cs) j =
fun t : ℝ => (c:ℝ)*(t^2*exp (-((j:ℝ)+3/2)*π*t))+finiteEnergyIntegrand cs (j+1) t`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.
-/
def integerSeries : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c::cs, a => (c:ℝ)+a*integerSeries cs a

/--
Exact identity `Polynomial.eval₂ (Int.castRingHom ℝ) a (integerPolynomial cs) = integerSeries
cs a`.

Use: `chebyshev2.SineContinuum.energyPolynomial3_value` rewrites with this identity to
establish exact identity `integerSeries energyCoefficients3 a = sigma₁Partial 3
a^6*sigma₂Partial 3 a^6`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.

Proof: Induct on `cs`; the recursive step uses the previous-stage assertion.
-/
theorem integerPolynomial_eval (cs : List ℤ) (a : ℝ) :
    Polynomial.eval₂ (Int.castRingHom ℝ) a (integerPolynomial cs) = integerSeries cs a := by
  induction cs with
  | nil => simp [integerPolynomial,integerSeries]
  | cons c cs ih => simp only [integerPolynomial,integerSeries,eval₂_add,eval₂_C,eval₂_mul,eval₂_X,ih,Int.coe_castRingHom]

/--
The literal truncated sixth-power product has the certified integer coefficients.

Exact identity `integerSeries energyCoefficients3 a = sigma₁Partial 3 a^6*sigma₂Partial 3 a^6`.

Use: `chebyshev2.SineContinuum.energy3_finite_integral` rewrites with this identity to
establish exact identity `energy3 = 512*∫ t in Ioi 1, t^2*exp (-3*π*t/2)*sigma₁Partial 3 (exp
(-π*t))^6*sigma₂Partial 3 (exp (-π*t))^6`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energyPolynomial3_exact`,
`chebyshev2.SineContinuum.integerPolynomial_eval` with the arguments shown in the proof.
-/
theorem energyPolynomial3_value (a : ℝ) :
    integerSeries energyCoefficients3 a = sigma₁Partial 3 a^6*sigma₂Partial 3 a^6 := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.energyPolynomial3_exact`,
  -- `chebyshev2.SineContinuum.integerPolynomial_eval` with the arguments shown in the
  -- proof.
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) a) energyPolynomial3_exact
  rw [integerPolynomial_eval] at h
  rw [h]
  simp only [energyPolynomial3,eval₂_mul,eval₂_pow,eval₂_add,eval₂_sub,eval₂_one,eval₂_ofNat,eval₂_X]
  simp only [sigma₁Partial,sigma₂Partial,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reducePow,pow_zero,pow_one,
    zero_add,add_zero,zero_mul,mul_zero,one_mul,mul_one]
  ring

/--
Defines `finiteEnergyIntegrand` of type `ℝ` by `t^2*exp (-((j:ℝ)+3/2)*π*t)*integerSeries cs
(exp (-π*t))`.

Use:
`_private.chebyshev2.SineContinuum.EnergyFiniteIntegral.0.chebyshev2.SineContinuum.finiteEnergyIntegrand_cons`
uses this definition to establish the identity `finiteEnergyIntegrand (c::cs) j = fun t : ℝ
=> (c:ℝ)*(t^2*exp (-((j:ℝ)+3/2)*π*t))+finiteEnergyIntegrand cs (j+1) t`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.
-/
def finiteEnergyIntegrand (cs : List ℤ) (j : ℕ) (t : ℝ) : ℝ :=
  t^2*exp (-((j:ℝ)+3/2)*π*t)*integerSeries cs (exp (-π*t))

/--
Exact identity `finiteEnergyIntegrand (c::cs) j = fun t : ℝ => (c:ℝ)*(t^2*exp
(-((j:ℝ)+3/2)*π*t))+finiteEnergyIntegrand cs (j+1) t`.

Use: `chebyshev2.SineContinuum.finiteEnergyIntegrand_integrable` rewrites with this
identity to establish integrability on the stated domain: `IntegrableOn (finiteEnergyIntegrand
cs j) (Ioi 1)`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
private theorem finiteEnergyIntegrand_cons (c : ℤ) (cs : List ℤ) (j : ℕ) :
    finiteEnergyIntegrand (c::cs) j = fun t : ℝ =>
      (c:ℝ)*(t^2*exp (-((j:ℝ)+3/2)*π*t))+finiteEnergyIntegrand cs (j+1) t := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  funext t
  unfold finiteEnergyIntegrand
  rw [integerSeries]
  have he : exp (-((j+1:ℕ)+3/2)*π*t) = exp (-((j:ℝ)+3/2)*π*t)*exp (-π*t) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/--
Integrability on the stated domain: `IntegrableOn (finiteEnergyIntegrand cs j) (Ioi 1)`.

Use: `chebyshev2.SineContinuum.finiteEnergyIntegrand_integral` rewrites with this
integrability result to establish the identity `(∫ t in Ioi 1, finiteEnergyIntegrand cs j t)
= weightedEnergy cs j`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.

Proof: Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
previous-stage assertion. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem finiteEnergyIntegrand_integrable (cs : List ℤ) (j : ℕ) :
    IntegrableOn (finiteEnergyIntegrand cs j) (Ioi 1) := by
  -- Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing j with
  | nil =>
    have hz : finiteEnergyIntegrand [] j = (0:ℝ → ℝ) := by
      funext t; simp [finiteEnergyIntegrand,integerSeries]
    rw [hz]
    exact integrable_zero ℝ ℝ (volume.restrict (Ioi 1))
  | cons c cs ih =>
    rw [finiteEnergyIntegrand_cons]
    exact (energyMoment_integrable (v := (j:ℝ)+3/2) (by positivity) |>.const_mul (c:ℝ)).add (ih (j+1))

/--
Integration of the finite polynomial gives exactly the sum of Lemma 7.

Exact identity `(∫ t in Ioi 1, finiteEnergyIntegrand cs j t) = weightedEnergy cs j`.

Use: `chebyshev2.SineContinuum.energy3_finite_integral` rewrites with this identity to
establish exact identity `energy3 = 512*∫ t in Ioi 1, t^2*exp (-3*π*t/2)*sigma₁Partial 3 (exp
(-π*t))^6*sigma₂Partial 3 (exp (-π*t))^6`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.

Proof: Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem finiteEnergyIntegrand_integral (cs : List ℤ) (j : ℕ) :
    (∫ t in Ioi 1, finiteEnergyIntegrand cs j t) = weightedEnergy cs j := by
  -- Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing j with
  | nil => simp [finiteEnergyIntegrand,integerSeries,weightedEnergy]
  | cons c cs ih =>
    rw [finiteEnergyIntegrand_cons,integral_add
      ((energyMoment_integrable (v := (j:ℝ)+3/2) (by positivity)).const_mul (c:ℝ))
      (finiteEnergyIntegrand_integrable cs (j+1)),integral_const_mul,
      energyMoment_integral (by positivity : (0:ℝ)<(j:ℝ)+3/2),ih,weightedEnergy]

/--
E_3 integrates the article's actual truncated series, not an unrelated approximation.

Exact identity `energy3 = 512*∫ t in Ioi 1, t^2*exp (-3*π*t/2)*sigma₁Partial 3 (exp
(-π*t))^6*sigma₂Partial 3 (exp (-π*t))^6`.

Use: `chebyshev2.SineContinuum.energyFiniteSum_three` rewrites with this identity to
establish exact identity `energyFiniteSum 3 = energy3`.

Article: chebyshev2, Lemma 7.

Proof: Use the identities/estimates
`chebyshev2.SineContinuum.finiteEnergyIntegrand_integral`,
`chebyshev2.SineContinuum.energyPolynomial3_value` with the arguments shown in the proof.
-/
theorem energy3_finite_integral :
    energy3 = 512*∫ t in Ioi 1,
      t^2*exp (-3*π*t/2)*sigma₁Partial 3 (exp (-π*t))^6*sigma₂Partial 3 (exp (-π*t))^6 := by
  -- Use the identities/estimates
  -- `chebyshev2.SineContinuum.finiteEnergyIntegrand_integral`,
  -- `chebyshev2.SineContinuum.energyPolynomial3_value` with the arguments shown in the
  -- proof.
  rw [energy3,← finiteEnergyIntegrand_integral energyCoefficients3 0]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  rw [finiteEnergyIntegrand,energyPolynomial3_value]
  norm_num only [Nat.cast_zero,zero_add]
  have he : -(3/2:ℝ)*π*t = -3*π*t/2 := by ring
  rw [he]
  ring

end
end chebyshev2.SineContinuum
