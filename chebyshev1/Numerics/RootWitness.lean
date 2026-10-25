import chebyshev1.Numerics.Intervals

/-!
Article: chebyshev1, Theorem 5.2.
Check endpoints by squaring, without recomputing a square root.
Use: `chebyshev1.Numerics.proposedRoot_correct` feeds
`chebyshev1.SineJacobi.ellipticWitnessValue_correct` (elliptic Witness Value correct).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.Numerics
open LeanCert.Core

/--
Dyadic endpoints proposed by an untrusted generator.

Use: `chebyshev1.Numerics.proposedRoot` uses this definition in the displayed construction
of `proposedRoot`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
abbrev RootWitness := ℤ × ℤ

/--
Candidate endpoints are nonnegative and ordered, independently of validity.

Use: `chebyshev1.Numerics.proposedRoot_correct` uses this definition to establish
membership in the specified domain/enclosure: `Real.sqrt x ∈ proposedRoot w`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def proposedRoot (w : RootWitness) : IntervalRat :=
  let a : ℚ := max (w.1/2^64) 0
  ⟨a, max a (w.2/2^64), le_max_left _ _⟩

/--
Check endpoints by squaring, without recomputing a square root.

Use: `chebyshev1.Numerics.proposedRoot_correct` rewrites with this definition to establish
membership in the specified domain/enclosure: `Real.sqrt x ∈ proposedRoot w`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def rootValid (I : IntervalRat) (w : RootWitness) : Bool :=
  decide ((proposedRoot w).lo^2 ≤ max I.lo 0 ∧ max I.hi 0 ≤ (proposedRoot w).hi^2)

/--
The stated quantitative bound `0 ≤ (proposedRoot w).lo`.

Use: `chebyshev1.Numerics.proposedRoot_correct` uses this bound to establish membership in
the specified domain/enclosure: `Real.sqrt x ∈ proposedRoot w`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem proposedRoot_nonneg (w : RootWitness) : 0 ≤ (proposedRoot w).lo := le_max_right _ _

/--
Membership in the specified domain/enclosure: `Real.sqrt x ∈ proposedRoot w`.

Use: `chebyshev1.SineJacobi.ellipticWitnessValue_correct` uses this assertion to establish
membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue ws`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.Numerics.proposedRoot_nonneg` with the
arguments shown in the proof.
-/
theorem proposedRoot_correct {x : ℝ} {I : IntervalRat} {w : RootWitness}
    (hx : x ∈ I) (h : rootValid I w = true) : Real.sqrt x ∈ proposedRoot w := by
  -- Use the identities/estimates `chebyshev1.Numerics.proposedRoot_nonneg` with the
  -- arguments shown in the proof.
  simp only [rootValid, decide_eq_true_eq] at h
  have hlo := max_le_max hx.1 (le_refl (0:ℝ))
  have hhi := max_le_max hx.2 (le_refl (0:ℝ))
  have ha : (0:ℝ) ≤ (proposedRoot w).lo := by exact_mod_cast proposedRoot_nonneg w
  have hab : ((proposedRoot w).lo:ℝ) ≤ (proposedRoot w).hi := by exact_mod_cast (proposedRoot w).le
  have hw : ((proposedRoot w).lo:ℝ)^2 ≤ max (I.lo:ℝ) 0 ∧
      max (I.hi:ℝ) 0 ≤ ((proposedRoot w).hi:ℝ)^2 := by exact_mod_cast h
  constructor <;> nlinarith [Real.sq_sqrt' (x := x), Real.sqrt_nonneg x, hw.1, hw.2]

end chebyshev1.Numerics
