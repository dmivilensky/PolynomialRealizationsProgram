import LeanCert.Core.IntervalRat.Basic
import Mathlib.Tactic

/-!
Article: chebyshev2, Section 4.1.
Integer witnesses for interval arithmetic.
Use: `chebyshev2.Numerics.IntegerCertificate.invCheck_sound` feeds
`chebyshev2.Numerics.IntegerCertificate.Op.check_sound` (check sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate
open LeanCert.Core
set_option autoImplicit false

/--
A raw pair of integer endpoints interpreted using an explicit scale. The data type permits
invalid pairs; checker-side validity and containment tests provide the required enclosure
properties.

Use: `chebyshev2.Numerics.IntegerCertificate.addCheck_sound` uses this record of data and
proof obligations to establish `R.Mem s (x + y)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Bounds where
  /-- Raw scaled lower endpoint; the checker imposes validity/order where required. -/
  lo : Int
  /-- Raw scaled upper endpoint; this data type alone does not certify an enclosure. -/
  hi : Int
  deriving Repr, DecidableEq, Inhabited

/--
Defines `Bounds.Mem` of type `Prop` by `(I.lo : ℝ) ≤ (s : ℝ) * x ∧ (s : ℝ) * x ≤ (I.hi : ℝ)`.

Use: `chebyshev2.Numerics.IntegerCertificate.addCheck_sound` uses this definition to
establish the precise assertion is `R.Mem s (x + y)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Bounds.Mem (I : Bounds) (s : ℕ) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ (s : ℝ) * x ∧ (s : ℝ) * x ≤ (I.hi : ℝ)

/--
Defines `valid` of type `Bool` by `decide (I.lo ≤ I.hi)`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.
-/
def valid (I : Bounds) : Bool := decide (I.lo ≤ I.hi)
/--
Defines `subset` of type `Bool` by `decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)`.

Use: `chebyshev2.Numerics.IntegerCertificate.subset_sound` uses this definition to
establish the precise assertion is `J.Mem s x`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def subset (I J : Bounds) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)
/--
Defines `negative` of type `Bool` by `decide (I.hi < 0)`.

Use: `chebyshev2.Numerics.IntegerCertificate.negative_sound` uses this definition to
establish the stated quantitative bound `x < 0`.

Article: chebyshev2, Section 4.1.
-/
def negative (I : Bounds) : Bool := decide (I.hi < 0)
/--
Defines `literalCheck` of type `Bool` by `decide (0 < d ∧ R.lo * (d : Int) ≤ n * (s : Int) ∧ n
* (s : Int) ≤ R.hi * (d : Int))`.

Use: `chebyshev2.Numerics.IntegerCertificate.literalCheck_sound` uses this definition to
establish the precise assertion is `R.Mem s ((n : ℝ) / d)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def literalCheck (s : ℕ) (n : Int) (d : ℕ) (R : Bounds) : Bool :=
  decide (0 < d ∧ R.lo * (d : Int) ≤ n * (s : Int) ∧
    n * (s : Int) ≤ R.hi * (d : Int))
/--
Defines `addCheck` of type `Bool` by `decide (R.lo ≤ A.lo + B.lo ∧ A.hi + B.hi ≤ R.hi)`.

Use: `chebyshev2.Numerics.IntegerCertificate.addCheck_sound` uses this definition to
establish the precise assertion is `R.Mem s (x + y)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def addCheck (A B R : Bounds) : Bool :=
  decide (R.lo ≤ A.lo + B.lo ∧ A.hi + B.hi ≤ R.hi)
/--
Defines `negCheck` of type `Bool` by `decide (R.lo ≤ -A.hi ∧ -A.lo ≤ R.hi)`.

Use: `chebyshev2.Numerics.IntegerCertificate.negCheck_sound` uses this definition to
establish the precise assertion is `R.Mem s (-x)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def negCheck (A R : Bounds) : Bool := decide (R.lo ≤ -A.hi ∧ -A.lo ≤ R.hi)
/--
Defines `mulCheck` of type `Bool` by `decide (R.lo * (s : Int) ≤ min (min (A.lo * B.lo) (A.lo *
B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)) ∧ max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi *
B.lo) (A.hi * B.hi)) ≤ R.hi * (s : Int))`.

Use: `chebyshev2.Numerics.IntegerCertificate.mulCheck_sound` uses this definition to
establish the precise assertion is `R.Mem s (x * y)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def mulCheck (s : ℕ) (A B R : Bounds) : Bool :=
  decide (R.lo * (s : Int) ≤
      min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)) ∧
    max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi)) ≤
      R.hi * (s : Int))

/--
Positive reciprocal. Negative reciprocals are expressed using negation.

Use: `chebyshev2.Numerics.IntegerCertificate.invCheck_sound` uses this definition to
establish the precise assertion is `R.Mem s x⁻¹`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def invCheck (s : ℕ) (A R : Bounds) : Bool :=
  decide (0 < A.lo ∧ 0 ≤ R.lo ∧ R.lo * A.hi ≤ (s : Int)^2 ∧
    (s : Int)^2 ≤ R.hi * A.lo)

/--
The precise assertion is `J.Mem s x`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this assertion to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem subset_sound {I J : Bounds} {s : ℕ} {x : ℝ}
    (h : subset I J = true) (hx : I.Mem s x) : J.Mem s x := by
  have hh : J.lo ≤ I.lo ∧ I.hi ≤ J.hi := of_decide_eq_true h
  have hl : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast hh.1
  have hu : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast hh.2
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

/--
The stated quantitative bound `x < 0`.

Use: `chebyshev2.Numerics.IntegerCertificate.programNegativeCheck_sound` uses this bound to
establish the stated quantitative bound `programValue v nodes 0 < 0`.

Article: chebyshev2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem negative_sound {I : Bounds} {s : ℕ} (hs : 0 < s) {x : ℝ}
    (h : negative I = true) (hx : I.Mem s x) : x < 0 := by
  have hh : I.hi < 0 := of_decide_eq_true h
  have hu : (I.hi : ℝ) < 0 := by exact_mod_cast hh
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  dsimp [Bounds.Mem] at hx
  nlinarith

/--
The precise assertion is `R.Mem s ((n : ℝ) / d)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this assertion to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem literalCheck_sound {s d : ℕ} {n : Int} {R : Bounds}
    (h : literalCheck s n d R = true) : R.Mem s ((n : ℝ) / d) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hh : 0 < d ∧ R.lo * (d : Int) ≤ n * (s : Int) ∧
      n * (s : Int) ≤ R.hi * (d : Int) := of_decide_eq_true h
  have hd : (0 : ℝ) < d := by exact_mod_cast hh.1
  have hl : (R.lo : ℝ) * d ≤ (n : ℝ) * s := by exact_mod_cast hh.2.1
  have hu : (n : ℝ) * s ≤ (R.hi : ℝ) * d := by exact_mod_cast hh.2.2
  dsimp [Bounds.Mem]
  rw [← mul_div_assoc]
  exact ⟨(le_div_iff₀ hd).mpr (by nlinarith), (div_le_iff₀ hd).mpr (by nlinarith)⟩

/--
The precise assertion is `R.Mem s (x + y)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this assertion to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem addCheck_sound {A B R : Bounds} {s : ℕ} {x y : ℝ}
    (h : addCheck A B R = true) (hx : A.Mem s x) (hy : B.Mem s y) :
    R.Mem s (x + y) := by
  have hh : R.lo ≤ A.lo + B.lo ∧ A.hi + B.hi ≤ R.hi := of_decide_eq_true h
  have hl : (R.lo : ℝ) ≤ A.lo + B.lo := by exact_mod_cast hh.1
  have hu : (A.hi : ℝ) + B.hi ≤ R.hi := by exact_mod_cast hh.2
  dsimp [Bounds.Mem] at *
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

/--
The precise assertion is `R.Mem s (-x)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this assertion to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem negCheck_sound {A R : Bounds} {s : ℕ} {x : ℝ}
    (h : negCheck A R = true) (hx : A.Mem s x) : R.Mem s (-x) := by
  have hh : R.lo ≤ -A.hi ∧ -A.lo ≤ R.hi := of_decide_eq_true h
  have hl : (R.lo : ℝ) ≤ -A.hi := by exact_mod_cast hh.1
  have hu : -(A.lo : ℝ) ≤ R.hi := by exact_mod_cast hh.2
  dsimp [Bounds.Mem] at *
  constructor <;> nlinarith [hx.1, hx.2]

/--
The precise assertion is `R.Mem s (x * y)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this assertion to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mulCheck_sound {A B R : Bounds} {s : ℕ} (hs : 0 < s) {x y : ℝ}
    (h : mulCheck s A B R = true) (hx : A.Mem s x) (hy : B.Mem s y) :
    R.Mem s (x * y) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have ha : A.lo ≤ A.hi := by exact_mod_cast hx.1.trans hx.2
  have hb : B.lo ≤ B.hi := by exact_mod_cast hy.1.trans hy.2
  let IA : IntervalRat := ⟨A.lo, A.hi, by exact_mod_cast ha⟩
  let IB : IntervalRat := ⟨B.lo, B.hi, by exact_mod_cast hb⟩
  have hxy := IntervalRat.mem_mul
    (show (s : ℝ) * x ∈ IA by simpa [IA, IntervalRat.mem_def, Bounds.Mem] using hx)
    (show (s : ℝ) * y ∈ IB by simpa [IB, IntervalRat.mem_def, Bounds.Mem] using hy)
  simp only [IntervalRat.mem_def, IntervalRat.mul, IntervalRat.min4,
    IntervalRat.max4, IA, IB, Rat.cast_mul, Rat.cast_intCast, Rat.cast_min, Rat.cast_max] at hxy
  have hh := of_decide_eq_true h
  change R.lo * (s : Int) ≤ _ ∧ _ ≤ R.hi * (s : Int) at hh
  have hl : (R.lo : ℝ) * s ≤
      min (min ((A.lo : ℝ) * B.lo) ((A.lo : ℝ) * B.hi))
        (min ((A.hi : ℝ) * B.lo) ((A.hi : ℝ) * B.hi)) := by exact_mod_cast hh.1
  have hu : max (max ((A.lo : ℝ) * B.lo) ((A.lo : ℝ) * B.hi))
      (max ((A.hi : ℝ) * B.lo) ((A.hi : ℝ) * B.hi)) ≤ (R.hi : ℝ) * s := by
    exact_mod_cast hh.2
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · apply (mul_le_mul_iff_right₀ hsr).mp
    convert hl.trans hxy.1 using 1 <;> ring
  · apply (mul_le_mul_iff_right₀ hsr).mp
    convert hxy.2.trans hu using 1 <;> ring

/--
The precise assertion is `R.Mem s x⁻¹`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this assertion to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem invCheck_sound {A R : Bounds} {s : ℕ} (hs : 0 < s) {x : ℝ}
    (h : invCheck s A R = true) (hx : A.Mem s x) : R.Mem s x⁻¹ := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have hh : 0 < A.lo ∧ 0 ≤ R.lo ∧ R.lo * A.hi ≤ (s : Int)^2 ∧
      (s : Int)^2 ≤ R.hi * A.lo := of_decide_eq_true h
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have ha : (0 : ℝ) < A.lo := by exact_mod_cast hh.1
  have hr : (0 : ℝ) ≤ R.lo := by exact_mod_cast hh.2.1
  have hl : (R.lo : ℝ) * A.hi ≤ (s : ℝ)^2 := by exact_mod_cast hh.2.2.1
  have hu : (s : ℝ)^2 ≤ (R.hi : ℝ) * A.lo := by exact_mod_cast hh.2.2.2
  have hxp : 0 < x := by nlinarith [hx.1]
  have hRp : (0 : ℝ) ≤ R.hi := by
    by_contra! hn
    nlinarith [mul_neg_of_neg_of_pos hn ha]
  have hl' := mul_le_mul_of_nonneg_left hx.2 hr
  have hu' := mul_le_mul_of_nonneg_left hx.1 hRp
  constructor
  · rw [← div_eq_mul_inv, le_div_iff₀ hxp]
    apply (mul_le_mul_iff_left₀ hsr).mp
    nlinarith
  · rw [← div_eq_mul_inv, div_le_iff₀ hxp]
    apply (mul_le_mul_iff_left₀ hsr).mp
    nlinarith

end chebyshev2.Numerics.IntegerCertificate
