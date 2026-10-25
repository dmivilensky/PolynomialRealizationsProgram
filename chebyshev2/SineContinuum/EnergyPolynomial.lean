import chebyshev2.SineContinuum.EnergyMoments

/-!
Article: chebyshev2, Proposition 10.
The literal remainder R_K in Lemma 7.
Use: `chebyshev2.SineContinuum.energyRemainder` feeds
`chebyshev2.SineContinuum.thetaEnergy_error3` (theta Energy error3).
Proof chain: `chebyshev2.SineContinuum.energyFiniteSum_error` — chebyshev2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 50000

/--
The integer polynomial in Proposition 10.

Use: `chebyshev2.SineContinuum.energyPolynomial3_exact` uses this definition to establish
exact identity `integerPolynomial energyCoefficients3 = energyPolynomial3`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.
-/
def energyPolynomial3 : Polynomial ℤ :=
  (1+Polynomial.X^2+Polynomial.X^6+Polynomial.X^12)^6*(1-2*Polynomial.X+2*Polynomial.X^4-2*Polynomial.X^9)^6

/--
Ascending coefficients, independently checked by the polynomial identity below.

Use: `chebyshev2.SineContinuum.energy3` uses this definition in the displayed construction
of `energy3`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.
-/
def energyCoefficients3 : List ℤ :=
  [1, -12, 66, -232, 627, -1452, 2982, -5544,
   9669, -16016, 25158, -38160, 56266, -80124, 111816, -153528,
   205248, -270756, 353318, -450816, 570153, -715068, 878622, -1072776,
   1301058, -1549536, 1837056, -2165336, 2510649, -2900664, 3336266, -3779136,
   4266285, -4799460, 5321316, -5884656, 6489961, -7054608, 7654374, -8285680,
   8847006, -9435396, 10035042, -10534296, 11049984, -11564132, 11949744, -12336264,
   12710858, -12931704, 13159206, -13364320, 13388271, -13431684, 13443738, -13281576,
   13150218, -12969928, 12631248, -12339048, 12015529, -11545296, 11123682, -10684336,
   10121676, -9645000, 9144374, -8531016, 8027628, -7506636, 6923436, -6440856,
   5927065, -5386212, 4952364, -4511608, 4043484, -3662424, 3282668, -2901264,
   2616516, -2308716, 1998936, -1778784, 1546088, -1334904, 1173504, -990176,
   838464, -733344, 619548, -514848, 436992, -356224, 296160, -258624,
   203568, -160320, 136320, -105760, 90240, -73344, 50720, -41280,
   35520, -27072, 21504, -14592, 9584, -9024, 8640, -4736,
   3264, -1920, 1344, -2304, 1344, -192, 384, 0,
   384, -384, 0, 0, 0, 0, 64]

/--
Defines `integerPolynomial` by pattern matching with result type `List ℤ → Polynomial ℤ`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.SineContinuum.energyPolynomial3_exact` uses this definition to establish
exact identity `integerPolynomial energyCoefficients3 = energyPolynomial3`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.
-/
def integerPolynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | c::cs => C c+Polynomial.X*integerPolynomial cs

/--
Exact identity `(integerPolynomial cs).coeff j = cs.getD j 0`.

Use: `chebyshev2.SineContinuum.energyPolynomial3_coeff` rewrites with this identity to
establish exact identity `energyPolynomial3.coeff j = energyCoefficients3.getD j 0`.

Article: chebyshev2, Proposition 10.

Proof: Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem integerPolynomial_coeff (cs : List ℤ) (j : ℕ) :
    (integerPolynomial cs).coeff j = cs.getD j 0 := by
  -- Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing j with
  | nil => simp [integerPolynomial]
  | cons c cs ih =>
    cases j with
    | zero => simp [integerPolynomial]
    | succ j => simp only [integerPolynomial,coeff_add,coeff_C,coeff_X_mul,
        List.getD_cons_succ,ih,ite_eq_right (Nat.succ_ne_zero j),zero_add]

/--
All coefficients are exact integers of the literal printed product.

Exact identity `integerPolynomial energyCoefficients3 = energyPolynomial3`.

Use: `chebyshev2.SineContinuum.energyPolynomial3_coeff` rewrites with this identity to
establish exact identity `energyPolynomial3.coeff j = energyCoefficients3.getD j 0`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energyPolynomial3_exact : integerPolynomial energyCoefficients3 = energyPolynomial3 := by
  set_option maxHeartbeats 0 in
  norm_num [integerPolynomial,energyCoefficients3,energyPolynomial3]
  ring

/--
Exact identity `energyCoefficients3.length = 127`.

Use: `chebyshev2.SineContinuum.energy3_article` rewrites with this identity to establish
exact identity `energy3 = 512*∑ j ∈ Finset.range 127, (energyPolynomial3.coeff
j:ℝ)*energyMoment ((j:ℝ)+3/2)`.

Article: chebyshev2, Proposition 10.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem energyCoefficients3_length : energyCoefficients3.length = 127 := by decide

/--
Exact identity `energyPolynomial3.coeff j = energyCoefficients3.getD j 0`.

Use: `chebyshev2.SineContinuum.energy3_article` rewrites with this identity to establish
exact identity `energy3 = 512*∑ j ∈ Finset.range 127, (energyPolynomial3.coeff
j:ℝ)*energyMoment ((j:ℝ)+3/2)`.

Article: chebyshev2, Proposition 10.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energyPolynomial3_exact`,
`chebyshev2.SineContinuum.integerPolynomial_coeff` with the arguments shown in the proof.
-/
theorem energyPolynomial3_coeff (j : ℕ) :
    energyPolynomial3.coeff j = energyCoefficients3.getD j 0 := by rw [← energyPolynomial3_exact,integerPolynomial_coeff]

/--
Defines `weightedEnergy` by pattern matching with result type `List ℤ → ℕ → ℝ`. The displayed
branches determine the recursive cases and their returned values.

Use: `chebyshev2.SineContinuum.energy3` uses this definition in the displayed construction
of `energy3`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.
-/
def weightedEnergy : List ℤ → ℕ → ℝ
  | [], _ => 0
  | c::cs, j => (c:ℝ)*energyMoment ((j:ℝ)+3/2)+weightedEnergy cs (j+1)

/--
Exact identity `weightedEnergy cs j = ∑ i ∈ Finset.range cs.length, (cs.getD i
0:ℝ)*energyMoment ((j+i:ℕ)+3/2)`.

Use: `chebyshev2.SineContinuum.energy3_article` rewrites with this identity to establish
exact identity `energy3 = 512*∑ j ∈ Finset.range 127, (energyPolynomial3.coeff
j:ℝ)*energyMoment ((j:ℝ)+3/2)`.

Article: chebyshev2, Proposition 10.

Proof: Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
previous-stage assertion. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem weightedEnergy_eq_sum (cs : List ℤ) (j : ℕ) :
    weightedEnergy cs j =
      ∑ i ∈ Finset.range cs.length, (cs.getD i 0:ℝ)*energyMoment ((j+i:ℕ)+3/2) := by
  -- Induct on `cs` while keeping `j` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing j with
  | nil => simp [weightedEnergy]
  | cons c cs ih =>
    rw [weightedEnergy,ih,List.length_cons,Finset.sum_range_succ']
    simp only [List.getD_cons_zero,List.getD_cons_succ,Nat.add_zero]
    push_cast
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    ring

/--
E_3, with the exact coefficients specified in Proposition 10.

Use: `chebyshev2.SineContinuum.energy3_article` rewrites with this definition to establish
exact identity `energy3 = 512*∑ j ∈ Finset.range 127, (energyPolynomial3.coeff
j:ℝ)*energyMoment ((j:ℝ)+3/2)`.

Article: chebyshev2, Lemma 7 via `chebyshev2.SineContinuum.energy3_finite_integral`.
-/
def energy3 : ℝ := 512*weightedEnergy energyCoefficients3 0

/--
Exact identity `energy3 = 512*∑ j ∈ Finset.range 127, (energyPolynomial3.coeff
j:ℝ)*energyMoment ((j:ℝ)+3/2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 10.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.weightedEnergy_eq_sum`,
`chebyshev2.SineContinuum.energyCoefficients3_length`,
`chebyshev2.SineContinuum.energyPolynomial3_coeff` with the arguments shown in the proof.
-/
theorem energy3_article : energy3 =
    512*∑ j ∈ Finset.range 127, (energyPolynomial3.coeff j:ℝ)*energyMoment ((j:ℝ)+3/2) := by
  rw [energy3,weightedEnergy_eq_sum,energyCoefficients3_length]
  simp only [Nat.zero_add,energyPolynomial3_coeff]

/--
The two uniform theta-series bounds in Lemma 7.

Use: `chebyshev2.SineContinuum.energyRemainder` uses this definition in the displayed
construction of `energyRemainder`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.
-/
def energyM₁ : ℝ := 1/(1-Real.exp (-2*Real.pi))
/--
Defines `energyM₂` of type `ℝ` by `1+2*Real.exp (-Real.pi)/(1-Real.exp (-3*Real.pi))`.

Use: `chebyshev2.SineContinuum.energyRemainder` uses this definition in the displayed
construction of `energyRemainder`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.
-/
def energyM₂ : ℝ := 1+2*Real.exp (-Real.pi)/(1-Real.exp (-3*Real.pi))

/--
The literal remainder R_K in Lemma 7.

Use: `chebyshev2.SineContinuum.energyErrorMajorant_integral` uses this definition to
establish exact identity `512*(∫ t in Ioi (1:ℝ), energyErrorMajorant K t) = energyRemainder K`.

Article: chebyshev2, Proposition 10 via `chebyshev2.SineContinuum.energyFiniteSum_error`.
-/
def energyRemainder (K : ℕ) : ℝ :=
  512*(6*energyM₁^5*energyM₂^6*energyMoment (3/2+(K+1:ℕ)*(K+2:ℕ)) /
        (1-Real.exp (-2*(K+2:ℕ)*Real.pi)) +
    12*energyM₁^6*energyM₂^5*energyMoment (3/2+(K+1:ℕ)^2) /
        (1-Real.exp (-(2*K+3:ℕ)*Real.pi)))

end
end chebyshev2.SineContinuum
