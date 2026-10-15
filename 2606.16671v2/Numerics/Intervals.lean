import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Core.IntervalDyadic

/-!
Article: 2606.16671v2, Theorem 5.2.
A candidate reciprocal, with validation independent of its endpoints.
Use: `«2606.16671v2».Numerics.inverseBounds_correct` feeds
`«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` (elliptic Witness Value correct).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».Numerics
open LeanCert.Core

/--
Outward rounding keeps intermediate rational denominators bounded.

Use: `«2606.16671v2».Numerics.invPositive` uses this definition in the displayed construction
of `invPositive`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def rounded (I : IntervalRat) : IntervalRat :=
  (IntervalDyadic.ofIntervalRat I (-64)).toIntervalRat

/--
Membership in the specified domain/enclosure: `x ∈ rounded I`.

Use: `«2606.16671v2».Numerics.inverseBounds_correct` uses this assertion to establish
membership in the specified domain/enclosure: `x⁻¹ ∈ inverseBounds I`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem mem_rounded {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : x ∈ rounded I :=
  IntervalDyadic.mem_toIntervalRat.mp (IntervalDyadic.mem_ofIntervalRat hx (-64))

/--
The stated quantitative bound `(IntervalRat.sqrtRatLowerPrec q 64 : ℝ) ≤ Real.sqrt q`.

Use: `«2606.16671v2».Numerics.mem_root` uses this bound to establish membership in the
specified domain/enclosure: `Real.sqrt x ∈ root I`.

Article: 2606.16671v2, Theorem 5.2.

Proof: Separate `0 ≤ q` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
private theorem lower_root (q : ℚ) :
    (IntervalRat.sqrtRatLowerPrec q 64 : ℝ) ≤ Real.sqrt q := by
  by_cases h : 0 ≤ q
  · exact IntervalRat.sqrtRatLowerPrec_le_sqrt h 64
  · simp [IntervalRat.sqrtRatLowerPrec, le_of_not_ge h, Real.sqrt_eq_zero_of_nonpos
      (show (q:ℝ) ≤ 0 by exact_mod_cast le_of_not_ge h)]

/--
The stated quantitative bound `Real.sqrt q ≤ (IntervalRat.sqrtRatUpperPrec q 64 : ℝ)`.

Use: `«2606.16671v2».Numerics.mem_root` uses this bound to establish membership in the
specified domain/enclosure: `Real.sqrt x ∈ root I`.

Article: 2606.16671v2, Theorem 5.2.

Proof: Separate `0 ≤ q` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
private theorem upper_root (q : ℚ) :
    Real.sqrt q ≤ (IntervalRat.sqrtRatUpperPrec q 64 : ℝ) := by
  by_cases h : 0 ≤ q
  · exact IntervalRat.sqrt_le_sqrtRatUpperPrec h 64
  · simp [IntervalRat.sqrtRatUpperPrec, le_of_not_ge h, Real.sqrt_eq_zero_of_nonpos
      (show (q:ℝ) ≤ 0 by exact_mod_cast le_of_not_ge h)]

/--
A tight square-root enclosure using LeanCert's proved integer square-root bounds.

Use: `«2606.16671v2».Numerics.mem_root` uses this definition to establish membership in the
specified domain/enclosure: `Real.sqrt x ∈ root I`.

Article: 2606.16671v2, Theorem 5.2.
-/
def root (I : IntervalRat) : IntervalRat :=
  rounded ⟨IntervalRat.sqrtRatLowerPrec I.lo 64, IntervalRat.sqrtRatUpperPrec I.hi 64, by
    exact_mod_cast (lower_root I.lo).trans
      ((Real.sqrt_le_sqrt (by exact_mod_cast I.le)).trans (upper_root I.hi))⟩

/--
Membership in the specified domain/enclosure: `Real.sqrt x ∈ root I`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 5.2.

Proof: Use the identities/estimates `«2606.16671v2».Numerics.mem_rounded`,
`_private.«2606.16671v2».Numerics.Intervals.0.«2606.16671v2».Numerics.lower_root`,
`_private.«2606.16671v2».Numerics.Intervals.0.«2606.16671v2».Numerics.upper_root` with the
arguments shown in the proof.
-/
theorem mem_root {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : Real.sqrt x ∈ root I :=
  mem_rounded ⟨(lower_root I.lo).trans (Real.sqrt_le_sqrt hx.1),
    (Real.sqrt_le_sqrt hx.2).trans (upper_root I.hi)⟩

/--
Division is certified only when the denominator interval is strictly positive.

Use: `«2606.16671v2».Numerics.mem_invPositive` uses this definition to establish membership in
the specified domain/enclosure: `x⁻¹ ∈ J`.

Article: 2606.16671v2, Theorem 5.2.
-/
def invPositive (I : IntervalRat) : Option IntervalRat :=
  if h : 0 < I.lo then
    some (rounded ⟨I.hi⁻¹, I.lo⁻¹, inv_anti₀ h I.le⟩)
  else none

/--
Membership in the specified domain/enclosure: `x⁻¹ ∈ J`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 5.2.

Proof: Use the identities/estimates `«2606.16671v2».Numerics.mem_rounded` with the arguments
shown in the proof.
-/
theorem mem_invPositive {x : ℝ} {I J : IntervalRat} (hx : x ∈ I)
    (h : invPositive I = some J) : x⁻¹ ∈ J := by
  -- Use the identities/estimates `«2606.16671v2».Numerics.mem_rounded` with the arguments
  -- shown in the proof.
  unfold invPositive at h
  split_ifs at h with hp
  · cases h
    apply mem_rounded
    have hp' : (0:ℝ) < I.lo := by exact_mod_cast hp
    have hx' := hp'.trans_le hx.1
    simpa only [IntervalRat.mem_def, Rat.cast_inv] using
      And.intro (inv_anti₀ hx' hx.2) (inv_anti₀ hp' hx.1)

/--
A candidate reciprocal, with validation independent of its endpoints.

Use: `«2606.16671v2».Numerics.inverseBounds_correct` uses this definition to establish
membership in the specified domain/enclosure: `x⁻¹ ∈ inverseBounds I`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def inverseBounds (I : IntervalRat) : IntervalRat :=
  rounded ⟨min I.lo⁻¹ I.hi⁻¹, max I.lo⁻¹ I.hi⁻¹, min_le_max⟩

/--
Membership in the specified domain/enclosure: `x⁻¹ ∈ inverseBounds I`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` uses this assertion to establish
membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».Numerics.mem_rounded` with the arguments
shown in the proof.
-/
theorem inverseBounds_correct {x : ℝ} {I : IntervalRat}
    (hx : x ∈ I) (hp : 0 < I.lo) : x⁻¹ ∈ inverseBounds I := by
  apply mem_rounded
  have hp' : (0:ℝ) < I.lo := by exact_mod_cast hp
  have hx' := hp'.trans_le hx.1
  simp only [IntervalRat.mem_def, Rat.cast_min, Rat.cast_max, Rat.cast_inv]
  exact ⟨(min_le_right _ _).trans (inv_anti₀ hx' hx.2),
    (inv_anti₀ hp' hx.1).trans (le_max_left _ _)⟩

end «2606.16671v2».Numerics
