import «2606.16671v2».Numerics.IntervalWitness

/-!
Article: 2606.16671v2, Theorem 5.2.
Small argument for Taylor evaluation; reconstruction uses six double-angle steps.
Use: `«2606.16671v2».Numerics.cosineWitnessValue_correct` feeds
`«2606.16671v2».SineJacobi.energyWitnessValue_correct` (energy Witness Value correct).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».Numerics
open LeanCert.Core

/--
Small argument for Taylor evaluation; reconstruction uses six double-angle steps.

Use: `«2606.16671v2».Numerics.cosineWitnessValid` uses this definition in the displayed
construction of `cosineWitnessValid`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def cosineInitial (I : IntervalRat) : IntervalRat :=
  rounded (IntervalRat.cosComputable (rounded (IntervalRat.scale (1/64) I)) 6)

/--
Defines `cosineDouble` of type `IntervalRat` by `rounded (IntervalRat.sub (IntervalRat.scale 2
(IntervalRat.pow I 2)) (IntervalRat.singleton 1))`.

Use: `_private.«2606.16671v2».Numerics.Cosine.0.«2606.16671v2».Numerics.cosineDouble_correct`
uses this definition to establish membership in the specified domain/enclosure: `Real.cos (2*x)
∈ cosineDouble I`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def cosineDouble (I : IntervalRat) : IntervalRat :=
  rounded (IntervalRat.sub (IntervalRat.scale 2 (IntervalRat.pow I 2)) (IntervalRat.singleton 1))

/--
Membership in the specified domain/enclosure: `Real.cos (2*x) ∈ cosineDouble I`.

Use: `_private.«2606.16671v2».Numerics.Cosine.0.«2606.16671v2».Numerics.doubleWitness_correct`
uses this assertion to establish membership in the specified domain/enclosure: `Real.cos
(2^ws.length*x) ∈ doubleWitnessValue I ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».Numerics.mem_rounded` with the arguments
shown in the proof.
-/
private theorem cosineDouble_correct {x : ℝ} {I : IntervalRat} (hx : Real.cos x ∈ I) :
    Real.cos (2*x) ∈ cosineDouble I := by
  have ho : (1:ℝ) ∈ IntervalRat.singleton 1 := by simpa using IntervalRat.mem_singleton 1
  simpa only [cosineDouble, Rat.cast_ofNat, Real.cos_two_mul] using
    mem_rounded (IntervalRat.mem_sub (IntervalRat.mem_scale 2 (IntervalRat.mem_pow hx 2)) ho)

/--
Defines `doubleWitnessValue` by pattern matching with result type `List IntervalWitness →
IntervalRat`. The displayed branches determine the recursive cases and their returned values.

Use: `_private.«2606.16671v2».Numerics.Cosine.0.«2606.16671v2».Numerics.doubleWitness_correct`
uses this definition to establish membership in the specified domain/enclosure: `Real.cos
(2^ws.length*x) ∈ doubleWitnessValue I ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def doubleWitnessValue (I : IntervalRat) : List IntervalWitness → IntervalRat
  | [] => I
  | w::ws => doubleWitnessValue (proposedInterval w) ws

/--
Defines `doubleWitnessValid` by pattern matching with result type `List IntervalWitness →
Bool`. The displayed branches determine the recursive cases and their returned values.

Use: `_private.«2606.16671v2».Numerics.Cosine.0.«2606.16671v2».Numerics.doubleWitness_correct`
rewrites with this definition to establish membership in the specified domain/enclosure:
`Real.cos (2^ws.length*x) ∈ doubleWitnessValue I ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def doubleWitnessValid (I : IntervalRat) : List IntervalWitness → Bool
  | [] => true
  | w::ws => intervalCovers (cosineDouble I) w && doubleWitnessValid (proposedInterval w) ws

/--
Membership in the specified domain/enclosure: `Real.cos (2^ws.length*x) ∈ doubleWitnessValue I
ws`.

Use: `«2606.16671v2».Numerics.cosineWitnessValue_correct` uses this assertion to establish
membership in the specified domain/enclosure: `Real.cos x ∈ cosineWitnessValue w`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Induct on `ws` while keeping `x I` arbitrary; the recursive step uses the
previous-stage assertion.
-/
private theorem doubleWitness_correct {x : ℝ} {I : IntervalRat} {ws : List IntervalWitness}
    (hx : Real.cos x ∈ I) (h : doubleWitnessValid I ws = true) :
    Real.cos (2^ws.length*x) ∈ doubleWitnessValue I ws := by
  -- Induct on `ws` while keeping `x I` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ws generalizing x I with
  | nil => simpa [doubleWitnessValue] using hx
  | cons w ws ih =>
    simp only [doubleWitnessValid, Bool.and_eq_true] at h
    have hc := intervalCovers_correct (cosineDouble_correct hx) h.1
    have ht := ih hc h.2
    simpa only [doubleWitnessValue, List.length_cons, pow_succ, mul_assoc] using ht

/--
Defines `CosineWitness` of type `` by `IntervalWitness × List IntervalWitness`.

Use: `«2606.16671v2».Numerics.cosineWitnessValid` uses this definition in the displayed
construction of `cosineWitnessValid`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
abbrev CosineWitness := IntervalWitness × List IntervalWitness

/--
Defines `cosineWitnessValue` of type `IntervalRat` by `doubleWitnessValue (proposedInterval
w.1) w.2`.

Use: `«2606.16671v2».Numerics.cosineWitnessValue_correct` uses this definition to establish
membership in the specified domain/enclosure: `Real.cos x ∈ cosineWitnessValue w`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def cosineWitnessValue (w : CosineWitness) : IntervalRat :=
  doubleWitnessValue (proposedInterval w.1) w.2

/--
Defines `cosineWitnessValid` of type `Bool` by `intervalCovers (cosineInitial I) w.1 && decide
(w.2.length = 6) && doubleWitnessValid (proposedInterval w.1) w.2`.

Use: `«2606.16671v2».Numerics.cosineWitnessValue_correct` rewrites with this definition to
establish membership in the specified domain/enclosure: `Real.cos x ∈ cosineWitnessValue w`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def cosineWitnessValid (I : IntervalRat) (w : CosineWitness) : Bool :=
  intervalCovers (cosineInitial I) w.1 && decide (w.2.length = 6) &&
    doubleWitnessValid (proposedInterval w.1) w.2

/--
Membership in the specified domain/enclosure: `Real.cos x ∈ cosineWitnessValue w`.

Use: `«2606.16671v2».SineJacobi.energyWitnessValue_correct` uses this assertion to establish
membership in the specified domain/enclosure: `energyDensity t ∈ energyWitnessValue ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».Numerics.mem_rounded`,
`«2606.16671v2».Numerics.intervalCovers_correct`,
`_private.«2606.16671v2».Numerics.Cosine.0.«2606.16671v2».Numerics.doubleWitness_correct` with
the arguments shown in the proof.
-/
theorem cosineWitnessValue_correct {x : ℝ} {I : IntervalRat} {w : CosineWitness}
    (hx : x ∈ I) (h : cosineWitnessValid I w = true) : Real.cos x ∈ cosineWitnessValue w := by
  -- Use the identities/estimates `«2606.16671v2».Numerics.mem_rounded`,
  -- `«2606.16671v2».Numerics.intervalCovers_correct`,
  -- `_private.«2606.16671v2».Numerics.Cosine.0.«2606.16671v2».Numerics.doubleWitness_correct`
  -- with the arguments shown in the proof.
  simp only [cosineWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at h
  have hs : x/64 ∈ rounded (IntervalRat.scale (1/64) I) := by
    convert mem_rounded (IntervalRat.mem_scale (1/64) hx) using 1; norm_num; ring
  have hc := intervalCovers_correct (mem_rounded (IntervalRat.mem_cosComputable hs 6)) h.1.1
  have ht := doubleWitness_correct hc h.2
  rw [h.1.2] at ht
  simpa only [cosineWitnessValue, show (2:ℝ)^6 = 64 by norm_num,
    show 64*(x/64) = x by ring] using ht

end «2606.16671v2».Numerics
