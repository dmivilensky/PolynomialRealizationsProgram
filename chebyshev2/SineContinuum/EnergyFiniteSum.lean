import chebyshev2.SineContinuum.EnergyArticle
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
Article: chebyshev2, Proposition 10.
The full finite-sum version of Lemma 7 for the original sine energy.
Result: `chebyshev2.SineContinuum.energyFiniteSum_tendsto` supplies the stated article
conclusion.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real Set MeasureTheory Polynomial
set_option backward.isDefEq.respectTransparency false

/--
The integer polynomial of Lemma 7 at an arbitrary truncation order.

Use: `chebyshev2.SineContinuum.energyFiniteSum` uses this definition in the displayed
construction of `energyFiniteSum`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.
-/
def energyPolynomial (K : ℕ) : Polynomial ℤ :=
  (∑ j ∈ Finset.range (K+1), Polynomial.X^(j*(j+1)))^6 *
    (1+C 2*(∑ j ∈ Finset.range K, C ((-1:ℤ)^(j+1))*Polynomial.X^((j+1)^2)))^6

/--
The stated quantitative bound `(energyPolynomial K).natDegree ≤ 12*K^2+6*K`.

Use: `chebyshev2.SineContinuum.energyFiniteSum_integral` uses this bound to establish exact
identity `energyFiniteSum K = 512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem energyPolynomial_degree (K : ℕ) : (energyPolynomial K).natDegree ≤ 12*K^2+6*K := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let P : Polynomial ℤ := ∑ j ∈ Finset.range (K+1), Polynomial.X^(j*(j+1))
  let Q : Polynomial ℤ := ∑ j ∈ Finset.range K, C ((-1:ℤ)^(j+1))*Polynomial.X^((j+1)^2)
  have hP : P.natDegree ≤ K*(K+1) := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    rw [natDegree_X_pow]
    have h : j ≤ K := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
    exact Nat.mul_le_mul h (Nat.add_le_add_right h 1)
  have hQ : Q.natDegree ≤ K^2 := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_X_pow]
    have h : j+1 ≤ K := Finset.mem_range.mp hj
    nlinarith
  have hS : (1+C 2*Q).natDegree ≤ K^2 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans hQ))
  change (P^6*(1+C 2*Q)^6).natDegree ≤ _
  have h := natDegree_mul_le (p:=P^6) (q:=(1+C 2*Q)^6)
  have hp := natDegree_pow_le (p:=P) (n:=6)
  have hq := natDegree_pow_le (p:=1+C 2*Q) (n:=6)
  nlinarith

/--
Exact identity `eval₂ (Int.castRingHom ℝ) a (energyPolynomial K) = sigma₁Partial K
a^6*sigma₂Partial K a^6`.

Use: `chebyshev2.SineContinuum.energyFiniteSum_integral` rewrites with this identity to
establish exact identity `energyFiniteSum K = 512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand K
t`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energyPolynomial_value (K : ℕ) (a : ℝ) :
    eval₂ (Int.castRingHom ℝ) a (energyPolynomial K) = sigma₁Partial K a^6*sigma₂Partial K a^6 := by
  simp only [energyPolynomial,eval₂_mul,eval₂_pow,eval₂_add,eval₂_one,eval₂_C,
    eval₂_finsetSum,eval₂_X,Int.coe_castRingHom,Int.cast_ofNat,Int.cast_pow,
    Int.cast_neg,Int.cast_one,sigma₁Partial,sigma₂Partial]

/--
The literal finite sum E_K, with the printed upper degree 12K^2+6K.

Use: `chebyshev2.SineContinuum.energyFiniteSum_integral` rewrites with this definition to
establish exact identity `energyFiniteSum K = 512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand K
t`.

Article: chebyshev2, Proposition 10 via
`chebyshev2.SineContinuum.energyFiniteSum_integral`.
-/
def energyFiniteSum (K : ℕ) : ℝ := 512*∑ j ∈ Finset.range (12*K^2+6*K+1),
  ((energyPolynomial K).coeff j:ℝ)*energyMoment ((j:ℝ)+3/2)

/--
Every truncation integral equals its finite integer-coefficient moment sum.

Exact identity `energyFiniteSum K = 512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t`.

Use: `chebyshev2.SineContinuum.energyFiniteSum_error` rewrites with this identity to
establish the stated quantitative bound `|SineJacobi.energy-energyFiniteSum K| ≤
energyRemainder K`.

Article: chebyshev2, Proposition 10.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem energyFiniteSum_integral (K : ℕ) : energyFiniteSum K =
    512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hp := energyPolynomial_degree K
  have he (t : ℝ) : partialEnergyIntegrand K t =
      ∑ j ∈ Finset.range (12*K^2+6*K+1), ((energyPolynomial K).coeff j:ℝ)*
        (t^2*exp (-((j:ℝ)+3/2)*π*t)) := by
    unfold partialEnergyIntegrand
    rw [mul_assoc (t^2*exp _),← energyPolynomial_value,
      eval₂_eq_sum_range' (Int.castRingHom ℝ) (Nat.lt_succ_of_le hp),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Int.coe_castRingHom]
    rw [← exp_nat_mul]
    have hx : exp (-((j:ℝ)+3/2)*π*t) = exp (-(3/2)*π*t)*exp ((j:ℝ)*(-π*t)) := by
      rw [← exp_add]; congr 1; ring
    rw [hx]
    ring
  rw [energyFiniteSum]
  congr 1
  simp_rw [he]
  rw [integral_finsetSum (f:=fun (j:ℕ) (t:ℝ) => ((energyPolynomial K).coeff j:ℝ)*
    (t^2*exp (-((j:ℝ)+3/2)*π*t))) _ (fun j _ =>
    (energyMoment_integrable (v:=(j:ℝ)+3/2) (by positivity)).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,energyMoment_integral (by positivity)]

/--
The arbitrary-order finite sum specializes to the certified E_3.

Exact identity `energyFiniteSum 3 = energy3`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 10.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energyFiniteSum_integral`,
`chebyshev2.SineContinuum.energy3_finite_integral` with the arguments shown in the proof.
-/
theorem energyFiniteSum_three : energyFiniteSum 3 = energy3 := by
  rw [energyFiniteSum_integral,energy3_finite_integral]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  unfold partialEnergyIntegrand
  rw [show -(3/2:ℝ)*π*t = -3*π*t/2 by ring]

/--
The full finite-sum version of Lemma 7 for the original sine energy.

The stated quantitative bound `|SineJacobi.energy-energyFiniteSum K| ≤ energyRemainder K`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Proposition 10.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energyFiniteSum_integral`,
`chebyshev2.SineContinuum.energy_error` with the arguments shown in the proof.
-/
theorem energyFiniteSum_error (K : ℕ) :
    |SineJacobi.energy-energyFiniteSum K| ≤ energyRemainder K := by
  rw [energyFiniteSum_integral]
  exact energy_error K

/--
The precise assertion is `Filter.Tendsto energyFiniteSum Filter.atTop (nhds
SineJacobi.energy)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Proposition 10.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem energyFiniteSum_tendsto : Filter.Tendsto energyFiniteSum Filter.atTop (nhds SineJacobi.energy) := by
  have he : energyFiniteSum = (fun K => 512*∫ t in Ioi (1:ℝ), partialEnergyIntegrand K t) :=
    funext energyFiniteSum_integral
  rw [he]
  exact energy_truncations_tendsto

end
end chebyshev2.SineContinuum
