import chebyshev2.Numerics.ExpHigh

/-!
Article: chebyshev2, Section 4.1.
Binary Power High.
Use: `chebyshev2.Numerics.mem_expBinaryHigh` feeds `chebyshev2.Numerics.logCoshCheck_sound`
(log Cosh Check sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open LeanCert.Core
set_option autoImplicit false

/--
Defines `powerBinaryHigh` of type `IntervalRat` by `if h : n=0 then IntervalRat.singleton 1
else let J := squareHigh (powerBinaryHigh I (n/2)) if n%2=0 then J else roundHigh
(IntervalRat.mul I J) termination_by n decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero
h) (by decide)`.

Use: `chebyshev2.Numerics.expPointBinaryHigh` uses this definition in the displayed
construction of `expPointBinaryHigh`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def powerBinaryHigh (I : IntervalRat) (n : ℕ) : IntervalRat :=
  if h : n=0 then IntervalRat.singleton 1
  else
    let J := squareHigh (powerBinaryHigh I (n/2))
    if n%2=0 then J else roundHigh (IntervalRat.mul I J)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/--
Membership in the specified domain/enclosure: `x^n∈powerBinaryHigh I n`.

Use: `chebyshev2.Numerics.mem_expPointBinaryHigh` uses this assertion to establish
membership in the specified domain/enclosure: `Real.exp (q:ℝ)∈expPointBinaryHigh q`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Separate `n=0` from
its negation; prove the goal under each of these mutually exclusive hypotheses.
-/
theorem mem_powerBinaryHigh {x : ℝ} {I : IntervalRat} (hx : x∈I) (n : ℕ) :
    x^n∈powerBinaryHigh I n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [powerBinaryHigh]
    by_cases hz : n=0
    · subst n
      rw [dite_eq_left rfl]
      simpa only [pow_zero,Rat.cast_one] using IntervalRat.mem_singleton 1
    · rw [dite_eq_right hz]
      have hm := ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))
      by_cases he : n%2=0
      · rw [ite_eq_left he]
        have hn : n=(n/2)*2 := by omega
        have heq : x^n=(x^(n/2))^2 :=
          (congrArg (fun m : ℕ => x^m) hn).trans (pow_mul x (n/2) 2)
        rw [heq]
        exact mem_squareHigh hm
      · rw [ite_eq_right he]
        have hn : n=(n/2)*2+1 := by omega
        have heq : x^n=x*(x^(n/2))^2 := by
          calc x^n=x^((n/2)*2+1) := congrArg (fun m : ℕ => x^m) hn
               _=x*(x^(n/2))^2 := by rw [pow_add,pow_mul,pow_one];ring
        rw [heq]
        exact mem_roundHigh (IntervalRat.mem_mul hx (mem_squareHigh hm))

/--
Defines `expPointBinaryHigh` of type `IntervalRat` by `powerBinaryHigh (expRawHigh
(q/(expHighMultiplicity q:ℚ)) 32) (expHighMultiplicity q)`.

Use: `chebyshev2.Numerics.expBinaryHigh` uses this definition in the displayed construction
of `expBinaryHigh`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def expPointBinaryHigh (q : ℚ) : IntervalRat :=
  powerBinaryHigh (expRawHigh (q/(expHighMultiplicity q:ℚ)) 32) (expHighMultiplicity q)

/--
Membership in the specified domain/enclosure: `Real.exp (q:ℝ)∈expPointBinaryHigh q`.

Use: `chebyshev2.Numerics.mem_expBinaryHigh` uses this assertion to establish membership in
the specified domain/enclosure: `Real.exp x∈expBinaryHigh I`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem mem_expPointBinaryHigh (q : ℚ) : Real.exp (q:ℝ)∈expPointBinaryHigh q := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hm : 0<expHighMultiplicity q := pow_pos (by decide) _
  have hm0 : (expHighMultiplicity q:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  have h := mem_powerBinaryHigh (mem_expRawHigh (q/(expHighMultiplicity q:ℚ)) 32) (expHighMultiplicity q)
  change Real.exp (q:ℝ)∈powerBinaryHigh (expRawHigh (q/(expHighMultiplicity q:ℚ)) 32) (expHighMultiplicity q)
  convert h using 1
  rw [←Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/--
Defines `expBinaryHigh` of type `IntervalRat` by `IntervalRat.hull (expPointBinaryHigh I.lo)
(expPointBinaryHigh I.hi)`.

Use: `chebyshev2.Numerics.mem_expBinaryHigh` rewrites with this definition to establish
membership in the specified domain/enclosure: `Real.exp x∈expBinaryHigh I`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def expBinaryHigh (I : IntervalRat) : IntervalRat :=
  IntervalRat.hull (expPointBinaryHigh I.lo) (expPointBinaryHigh I.hi)

/--
Membership in the specified domain/enclosure: `Real.exp x∈expBinaryHigh I`.

Use: `chebyshev2.Numerics.logCoshCheck_sound` uses this assertion to establish membership
in the specified domain/enclosure: `Real.log (Real.cosh x)∈output`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_expPointBinaryHigh` with the
arguments shown in the proof.
-/
theorem mem_expBinaryHigh {I : IntervalRat} {x : ℝ} (hx : x∈I) : Real.exp x∈expBinaryHigh I := by
  have hl := mem_expPointBinaryHigh I.lo
  have hu := mem_expPointBinaryHigh I.hi
  simp only [expBinaryHigh,IntervalRat.hull,IntervalRat.mem_def,Rat.cast_min,Rat.cast_max]
  exact ⟨(min_le_left _ _).trans (hl.1.trans (Real.exp_le_exp.mpr hx.1)),
    (Real.exp_le_exp.mpr hx.2).trans (hu.2.trans (le_max_right _ _))⟩

end chebyshev2.Numerics
