import chebyshev2.Numerics.IntervalJet

/-!
Article: chebyshev2, Section 4.1.
Rounded exponential evaluation for ODE certificates.
Use: `chebyshev2.Numerics.expHighMultiplicity` feeds
`chebyshev2.Numerics.mem_expPointBinaryHigh` (mem exp Point Binary High).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `expPolynomialHigh` of type `IntervalRat` by `sumIntervals (fun j => roundHigh
(IntervalRat.mul (IntervalRat.singleton (1/(j.factorial:ℚ))) (powerHigh (IntervalRat.singleton
q) j))) (n+1)`.

Use: `chebyshev2.Numerics.expRawHigh` uses this definition in the displayed construction of
`expRawHigh`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def expPolynomialHigh (q : ℚ) (n : ℕ) : IntervalRat :=
  sumIntervals (fun j => roundHigh (IntervalRat.mul
    (IntervalRat.singleton (1/(j.factorial:ℚ))) (powerHigh (IntervalRat.singleton q) j))) (n+1)

/--
Defines `expRemainderHigh` of type `IntervalRat` by `roundHigh (IntervalRat.mul
(IntervalRat.singleton ((3:ℚ)^(Nat.ceil |q|+1)/((n+1).factorial:ℚ))) (powerHigh
(IntervalRat.singleton |q|) (n+1)))`.

Use: `chebyshev2.Numerics.expRawHigh` uses this definition in the displayed construction of
`expRawHigh`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def expRemainderHigh (q : ℚ) (n : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.mul
    (IntervalRat.singleton ((3:ℚ)^(Nat.ceil |q|+1)/((n+1).factorial:ℚ)))
    (powerHigh (IntervalRat.singleton |q|) (n+1)))

/--
Defines `expRawHigh` of type `IntervalRat` by `let r := max 0 (expRemainderHigh q n).hi
roundHigh (IntervalRat.add (expPolynomialHigh q n) ⟨-r,r,neg_le_self (le_max_left _ _)⟩)`.

Use: `chebyshev2.Numerics.expPointHigh` uses this definition in the displayed construction
of `expPointHigh`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def expRawHigh (q : ℚ) (n : ℕ) : IntervalRat :=
  let r := max 0 (expRemainderHigh q n).hi
  roundHigh (IntervalRat.add (expPolynomialHigh q n) ⟨-r,r,neg_le_self (le_max_left _ _)⟩)

/--
Membership in the specified domain/enclosure: `Real.exp (q:ℝ)∈expRawHigh q n`.

Use: `chebyshev2.Numerics.mem_expPointHigh` uses this assertion to establish membership in
the specified domain/enclosure: `Real.exp (q:ℝ)∈expPointHigh q`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_sumIntervals`,
`chebyshev2.Numerics.mem_roundHigh`, `chebyshev2.Numerics.mem_powerHigh` with the
arguments shown in the proof.
-/
theorem mem_expRawHigh (q : ℚ) (n : ℕ) : Real.exp (q:ℝ)∈expRawHigh q n := by
  -- Use the identities/estimates `chebyshev2.Numerics.mem_sumIntervals`,
  -- `chebyshev2.Numerics.mem_roundHigh`, `chebyshev2.Numerics.mem_powerHigh` with the
  -- arguments shown in the proof.
  let P : ℝ := ∑ j∈Finset.range (n+1),(1/(j.factorial:ℝ))*(q:ℝ)^j
  have hP : P∈expPolynomialHigh q n := by
    apply mem_sumIntervals
    intro j _
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using
      mem_roundHigh (IntervalRat.mem_mul (IntervalRat.mem_singleton (1/(j.factorial:ℚ)))
        (mem_powerHigh (IntervalRat.mem_singleton q) j))
  have hR : (((3:ℚ)^(Nat.ceil |q|+1)*|q|^(n+1)/((n+1).factorial:ℚ):ℚ):ℝ)
      ∈expRemainderHigh q n := by
    apply mem_roundHigh
    have hm := IntervalRat.mem_mul
      (IntervalRat.mem_singleton ((3:ℚ)^(Nat.ceil |q|+1)/((n+1).factorial:ℚ)))
      (mem_powerHigh (IntervalRat.mem_singleton |q|) (n+1))
    convert hm using 1
    push_cast
    ring
  have hr := IntervalRat.exp_taylor_remainder_in_interval (IntervalRat.mem_singleton q) n
  have hr' : -(((3:ℚ)^(Nat.ceil |q|+1)*|q|^(n+1)/((n+1).factorial:ℚ):ℚ):ℝ)≤
      Real.exp (q:ℝ)-P ∧ Real.exp (q:ℝ)-P≤
      (((3:ℚ)^(Nat.ceil |q|+1)*|q|^(n+1)/((n+1).factorial:ℚ):ℚ):ℝ) := by
    simpa only [IntervalRat.expRemainderBoundComputable,IntervalRat.maxAbs,IntervalRat.singleton,
      max_self,IntervalRat.ratFactorial,IntervalRat.mem_def,Rat.cast_neg,
      iteratedDeriv_eq_iterate,Real.iter_deriv_exp,Real.exp_zero] using hr
  have hbound : ((expRemainderHigh q n).hi:ℝ)≤(max 0 (expRemainderHigh q n).hi:ℚ) := by
    exact_mod_cast le_max_right (0:ℚ) (expRemainderHigh q n).hi
  have hm : Real.exp (q:ℝ)-P∈(⟨-max 0 (expRemainderHigh q n).hi,
      max 0 (expRemainderHigh q n).hi,neg_le_self (le_max_left _ _)⟩:IntervalRat) := by
    simp only [IntervalRat.mem_def,Rat.cast_neg]
    exact ⟨(neg_le_neg (hR.2.trans hbound)).trans hr'.1,hr'.2.trans (hR.2.trans hbound)⟩
  simpa only [expRawHigh,add_sub_cancel] using mem_roundHigh (IntervalRat.mem_add hP hm)

/--
Defines `expHighMultiplicity` of type `ℕ` by `2^(Nat.log2 (Nat.ceil |q|+1)+3)`.

Use: `chebyshev2.Numerics.expPointHigh` uses this definition in the displayed construction
of `expPointHigh`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def expHighMultiplicity (q : ℚ) : ℕ := 2^(Nat.log2 (Nat.ceil |q|+1)+3)

/--
Defines `expPointHigh` of type `IntervalRat` by `powerHigh (expRawHigh (q/(expHighMultiplicity
q:ℚ)) 32) (expHighMultiplicity q)`.

Use: `chebyshev2.Numerics.expHigh` uses this definition in the displayed construction of
`expHigh`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
def expPointHigh (q : ℚ) : IntervalRat :=
  powerHigh (expRawHigh (q/(expHighMultiplicity q:ℚ)) 32) (expHighMultiplicity q)

/--
Membership in the specified domain/enclosure: `Real.exp (q:ℝ)∈expPointHigh q`.

Use: `chebyshev2.Numerics.mem_expHigh` uses this assertion to establish membership in the
specified domain/enclosure: `Real.exp x∈expHigh I`.

Article: chebyshev2, Section 4.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem mem_expPointHigh (q : ℚ) : Real.exp (q:ℝ)∈expPointHigh q := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hm : 0<expHighMultiplicity q := pow_pos (by decide) _
  have hm0 : (expHighMultiplicity q:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  have h := mem_powerHigh (mem_expRawHigh (q/(expHighMultiplicity q:ℚ)) 32) (expHighMultiplicity q)
  change Real.exp (q:ℝ)∈powerHigh (expRawHigh (q/(expHighMultiplicity q:ℚ)) 32) (expHighMultiplicity q)
  convert h using 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/--
Defines `expHigh` of type `IntervalRat` by `IntervalRat.hull (expPointHigh I.lo) (expPointHigh
I.hi)`.

Use: `chebyshev2.Numerics.mem_expHigh` rewrites with this definition to establish
membership in the specified domain/enclosure: `Real.exp x∈expHigh I`.

Article: chebyshev2, Section 4.1.
-/
def expHigh (I : IntervalRat) : IntervalRat :=
  IntervalRat.hull (expPointHigh I.lo) (expPointHigh I.hi)

/--
Membership in the specified domain/enclosure: `Real.exp x∈expHigh I`.

Use: `chebyshev2.Numerics.FlowStep.check_range_sound` uses this assertion to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_expPointHigh` with the
arguments shown in the proof.
-/
theorem mem_expHigh {I : IntervalRat} {x : ℝ} (hx : x∈I) : Real.exp x∈expHigh I := by
  have hl := mem_expPointHigh I.lo
  have hu := mem_expPointHigh I.hi
  simp only [expHigh,IntervalRat.hull,IntervalRat.mem_def,Rat.cast_min,Rat.cast_max]
  exact ⟨(min_le_left _ _).trans (hl.1.trans (Real.exp_le_exp.mpr hx.1)),
    (Real.exp_le_exp.mpr hx.2).trans (hu.2.trans (le_max_right _ _))⟩

end chebyshev2.Numerics
