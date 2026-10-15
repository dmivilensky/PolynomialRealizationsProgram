import «2606.16671v2».SineJacobi.EllipticDescent
import «2606.16671v2».Numerics.RootWitness
import «2606.16671v2».Numerics.IntervalWitness

/-!
Article: 2606.16671v2, Theorem 5.2.
Every supplied enclosure is checked using only neighboring supplied data.
Use: `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` feeds
`«2606.16671v2».SineJacobi.ellipticWitnessBounds_correct` (elliptic Witness Bounds correct).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
open LeanCert.Core «2606.16671v2».Numerics

/--
Defines `positivePart` of type `IntervalRat` by `⟨max I.lo 0, max I.hi 0, max_le_max I.le
le_rfl⟩`.

Use:
`_private.«2606.16671v2».SineJacobi.EllipticWitnesses.0.«2606.16671v2».SineJacobi.mem_positivePart`
uses this definition to establish membership in the specified domain/enclosure: `x ∈
positivePart I`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
private def positivePart (I : IntervalRat) : IntervalRat :=
  ⟨max I.lo 0, max I.hi 0, max_le_max I.le le_rfl⟩

/--
Membership in the specified domain/enclosure: `x ∈ positivePart I`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` uses this assertion to establish
membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem mem_positivePart {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hp : 0 ≤ x) :
    x ∈ positivePart I := by
  simpa only [positivePart, IntervalRat.mem_def, Rat.cast_max, Rat.cast_zero] using
    And.intro (max_le hx.1 hp) (hx.2.trans (le_max_left _ _))

/--
Defines `modulusBounds` of type `IntervalRat` by `let R := proposedRoot w positivePart (rounded
(IntervalRat.mul (IntervalRat.sub (IntervalRat.singleton 1) R) (inverseBounds (IntervalRat.add
(IntervalRat.singleton 1) R))))`.

Use: `«2606.16671v2».SineJacobi.descentBounds` uses this definition in the displayed
construction of `descentBounds`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def modulusBounds (w : RootWitness) : IntervalRat :=
  let R := proposedRoot w
  positivePart (rounded (IntervalRat.mul (IntervalRat.sub (IntervalRat.singleton 1) R)
    (inverseBounds (IntervalRat.add (IntervalRat.singleton 1) R))))

/--
Defines `residualBounds` of type `IntervalRat` by `⟨1, max 1 (inverseBounds (proposedRoot
w)).hi, le_max_left _ _⟩`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` rewrites with this definition to
establish membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue
ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def residualBounds (w : RootWitness) : IntervalRat :=
  ⟨1, max 1 (inverseBounds (proposedRoot w)).hi, le_max_left _ _⟩

/--
Defines `descentBounds` of type `IntervalRat` by `rounded (IntervalRat.mul (IntervalRat.add
(IntervalRat.singleton 1) (modulusBounds w)) A)`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` uses this definition to establish
membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def descentBounds (w : RootWitness) (A : IntervalRat) : IntervalRat :=
  rounded (IntervalRat.mul (IntervalRat.add (IntervalRat.singleton 1) (modulusBounds w)) A)

/--
Each step supplies a root and an enclosure for the remaining elliptic value.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessBounds` uses this definition in the displayed
construction of `ellipticWitnessBounds`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
abbrev EllipticWitness := RootWitness × IntervalWitness

/--
Defines `ellipticWitnessValue` by pattern matching with result type `List EllipticWitness →
IntervalRat`. The displayed branches determine the recursive cases and their returned values.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessBounds` uses this definition in the displayed
construction of `ellipticWitnessBounds`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def ellipticWitnessValue : List EllipticWitness → IntervalRat
  | [] => IntervalRat.singleton 1
  | w::_ => proposedInterval w.2

/--
Every supplied enclosure is checked using only neighboring supplied data.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessBounds` uses this definition in the displayed
construction of `ellipticWitnessBounds`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def ellipticWitnessValid : List EllipticWitness → IntervalRat → Bool
  | [], _ => false
  | [w], I => rootValid (IntervalRat.sub (IntervalRat.singleton 1) I) w.1 &&
      decide (0 < (proposedRoot w.1).lo) && intervalCovers (residualBounds w.1) w.2
  | w::v::ws, I => rootValid (IntervalRat.sub (IntervalRat.singleton 1) I) w.1 &&
      intervalCovers (descentBounds w.1 (proposedInterval v.2)) w.2 &&
      ellipticWitnessValid (v::ws) (rounded (IntervalRat.pow (modulusBounds w.1) 2))

/--
Defines `ellipticWitnessBounds` of type `Option IntervalRat` by `if ellipticWitnessValid ws I
then some (ellipticWitnessValue ws) else none`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessBounds_correct` uses this definition to
establish membership in the specified domain/enclosure: `ellipticA x ∈ A`.

Article: 2606.16671v2, Theorem 5.2.
-/
def ellipticWitnessBounds (ws : List EllipticWitness) (I : IntervalRat) : Option IntervalRat :=
  if ellipticWitnessValid ws I then some (ellipticWitnessValue ws) else none

/--
Membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue ws`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessBounds_correct` uses this assertion to establish
membership in the specified domain/enclosure: `ellipticA x ∈ A`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Induct on `ws` while keeping `x I` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem ellipticWitnessValue_correct {ws : List EllipticWitness} {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hr : x ∈ Set.Ico (0:ℝ) 1) (h : ellipticWitnessValid ws I = true) :
    ellipticA x ∈ ellipticWitnessValue ws := by
  -- Induct on `ws` while keeping `x I` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ws generalizing x I with
  | nil => simp [ellipticWitnessValid] at h
  | cons w ws ih =>
    have ho : (1:ℝ) ∈ IntervalRat.singleton 1 := by simpa using IntervalRat.mem_singleton 1
    cases ws with
    | nil =>
      simp only [ellipticWitnessValid, Bool.and_eq_true, decide_eq_true_eq] at h
      have hs := proposedRoot_correct (IntervalRat.mem_sub ho hx) h.1.1
      have hi := inverseBounds_correct hs h.1.2
      have hb := ellipticA_bounds hr
      apply intervalCovers_correct (I := residualBounds w.1) _ h.2
      simp only [residualBounds, IntervalRat.mem_def, Rat.cast_one, Rat.cast_max]
      exact ⟨hb.1, (hb.2.trans (by simpa only [one_div] using hi.2)).trans (le_max_right _ _)⟩
    | cons v vs =>
      simp only [ellipticWitnessValid, Bool.and_eq_true] at h
      have hs := proposedRoot_correct (IntervalRat.mem_sub ho hx) h.1.1
      have hq : descendingModulus x ∈ modulusBounds w.1 := by
        have hp : 0 < (IntervalRat.add (IntervalRat.singleton 1) (proposedRoot w.1)).lo := by
          simp only [IntervalRat.add, IntervalRat.singleton]
          linarith [proposedRoot_nonneg w.1]
        have hi := inverseBounds_correct (IntervalRat.mem_add ho hs) hp
        apply mem_positivePart _ (descendingModulus_range hr).1
        simpa only [descendingModulus, div_eq_mul_inv] using
          mem_rounded (IntervalRat.mem_mul (IntervalRat.mem_sub ho hs) hi)
      have hqr := descendingModulus_range hr
      have hb := ih (mem_rounded (IntervalRat.mem_pow hq 2))
        ⟨sq_nonneg _, by nlinarith [hqr.1, hqr.2]⟩ h.2
      apply intervalCovers_correct (I := descentBounds w.1 (proposedInterval v.2)) _ h.1.2
      rw [ellipticA_descent hr]
      exact mem_rounded (IntervalRat.mem_mul (IntervalRat.mem_add ho hq) hb)

/--
Membership in the specified domain/enclosure: `ellipticA x ∈ A`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 5.2.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct`
with the arguments shown in the proof.
-/
theorem ellipticWitnessBounds_correct {ws : List EllipticWitness} {x : ℝ} {I A : IntervalRat}
    (hx : x ∈ I) (hr : x ∈ Set.Ico (0:ℝ) 1) (h : ellipticWitnessBounds ws I = some A) :
    ellipticA x ∈ A := by
  unfold ellipticWitnessBounds at h
  split_ifs at h with hv
  cases h
  exact ellipticWitnessValue_correct hx hr hv

end «2606.16671v2».SineJacobi
