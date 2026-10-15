import «2606.16671v2».Numerics.Intervals

/-!
Article: 2606.16671v2, Theorem 5.2.
Candidate conversion; correctness is supplied by `intervalCovers`, not the generator.
Use: `«2606.16671v2».Numerics.intervalCovers_correct` feeds
`«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` (elliptic Witness Value correct).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».Numerics
open LeanCert.Core

/--
Defines `IntervalWitness` of type `` by `ℤ × ℤ`.

Use: `«2606.16671v2».Numerics.intervalCovers` uses this definition in the displayed
construction of `intervalCovers`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
abbrev IntervalWitness := ℤ × ℤ

/--
Defines `proposedInterval` of type `IntervalRat` by `⟨min (w.1/2^64) (w.2/2^64), max (w.1/2^64)
(w.2/2^64), min_le_max⟩`.

Use: `«2606.16671v2».Numerics.intervalCovers` uses this definition in the displayed
construction of `intervalCovers`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def proposedInterval (w : IntervalWitness) : IntervalRat :=
  ⟨min (w.1/2^64) (w.2/2^64), max (w.1/2^64) (w.2/2^64), min_le_max⟩

/--
Defines `intervalCovers` of type `Bool` by `decide ((proposedInterval w).lo ≤ I.lo ∧ I.hi ≤
(proposedInterval w).hi)`.

Use: `«2606.16671v2».Numerics.intervalCovers_correct` rewrites with this definition to
establish membership in the specified domain/enclosure: `x ∈ proposedInterval w`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def intervalCovers (I : IntervalRat) (w : IntervalWitness) : Bool :=
  decide ((proposedInterval w).lo ≤ I.lo ∧ I.hi ≤ (proposedInterval w).hi)

/--
Membership in the specified domain/enclosure: `x ∈ proposedInterval w`.

Use: `_private.«2606.16671v2».Numerics.Cosine.0.«2606.16671v2».Numerics.doubleWitness_correct`
uses this assertion to establish membership in the specified domain/enclosure: `Real.cos
(2^ws.length*x) ∈ doubleWitnessValue I ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem intervalCovers_correct {x : ℝ} {I : IntervalRat} {w : IntervalWitness}
    (hx : x ∈ I) (h : intervalCovers I w = true) : x ∈ proposedInterval w := by
  simp only [intervalCovers, decide_eq_true_eq] at h
  have hl : ((proposedInterval w).lo:ℝ) ≤ I.lo := by exact_mod_cast h.1
  have hu : (I.hi:ℝ) ≤ (proposedInterval w).hi := by exact_mod_cast h.2
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

/--
Candidate conversion; correctness is supplied by `intervalCovers`, not the generator.

Use: `«2606.16671v2».Numerics.cosineWitnessCandidate` uses this definition in the displayed
construction of `cosineWitnessCandidate`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2.
-/
def intervalWitness (I : IntervalRat) : IntervalWitness :=
  ((I.lo*2^64).floor, (I.hi*2^64).ceil)

end «2606.16671v2».Numerics
