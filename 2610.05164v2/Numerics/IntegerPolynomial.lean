import «2610.05164v2».Numerics.IntegerEval
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: 2610.05164v2, Section 4.1.
Computed, outward rounded polynomial arithmetic.
Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Encloses` feeds
`«2610.05164v2».Numerics.IntegerCertificate.Poly.evalProgram_sound` (eval Program sound).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate.Poly
open Polynomial
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `zero` of type `Bounds` by `⟨0, 0⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.mul_sound` uses this definition to
establish the precise assertion is `Rep s out (p*q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def zero : Bounds := ⟨0, 0⟩
/--
Defines `addB` of type `Bounds` by `⟨a.lo+b.lo, a.hi+b.hi⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.addB_sound` rewrites with this definition
to establish `(addB a b).Mem s (x+y)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def addB (a b : Bounds) : Bounds := ⟨a.lo+b.lo, a.hi+b.hi⟩
/--
Defines `negB` of type `Bounds` by `⟨-a.hi, -a.lo⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.neg` uses this definition in the
displayed construction of `neg`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def negB (a : Bounds) : Bounds := ⟨-a.hi, -a.lo⟩
/--
Defines `roundedMul` of type `Bounds` by `let lo := min (min (a.lo*b.lo) (a.lo*b.hi)) (min
(a.hi*b.lo) (a.hi*b.hi)) let hi := max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo)
(a.hi*b.hi)) ⟨lo/s,ceilDiv hi s⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.mulB` uses this definition in the
displayed construction of `mulB`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def roundedMul (s : Nat) (a b : Bounds) : Bounds :=
  let lo := min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
  let hi := max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))
  ⟨lo/s,ceilDiv hi s⟩
/--
Defines `mulB` of type `Option Bounds` by `some (roundedMul s a b)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.mulB_sound` uses this definition to
establish the precise assertion is `r.Mem s (x*y)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def mulB (s : Nat) (a b : Bounds) : Option Bounds := some (roundedMul s a b)

/--
The precise assertion is `zero.Mem s 0`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.derivative_sound` uses this assertion to
establish the precise assertion is `Rep s (derivative as) p.derivative`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem zero_mem (s : Nat) : zero.Mem s 0 := by simp [zero, Bounds.Mem]
/--
The precise assertion is `(addB a b).Mem s (x+y)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.add_sound` uses this assertion to
establish the precise assertion is `Rep s (add as bs) (p+q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.addCheck_sound`
with the arguments shown in the proof.
-/
theorem addB_sound {s : Nat} {a b : Bounds} {x y : ℝ}
    (ha : a.Mem s x) (hb : b.Mem s y) : (addB a b).Mem s (x+y) :=
  addCheck_sound (by simp [addCheck, addB]) ha hb
/--
The precise assertion is `(negB a).Mem s (-x)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.neg_sound` uses this assertion to
establish the precise assertion is `Rep s (neg as) (-p)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.negCheck_sound`
with the arguments shown in the proof.
-/
theorem negB_sound {s : Nat} {a : Bounds} {x : ℝ}
    (ha : a.Mem s x) : (negB a).Mem s (-x) :=
  negCheck_sound (by simp [negCheck, negB]) ha
/--
The precise assertion is `r.Mem s (x*y)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound` uses this assertion to
establish the precise assertion is `out.Mem s (p.eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.mulCheck_sound`
with the arguments shown in the proof.
-/
theorem mulB_sound {s : Nat} (hs : 0 < s) {a b r : Bounds} {x y : ℝ}
    (ha : a.Mem s x) (hb : b.Mem s y) (hc : mulB s a b = some r) :
    r.Mem s (x*y) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.mulCheck_sound`
  -- with the arguments shown in the proof.
  have hr : roundedMul s a b=r := by simpa [mulB] using hc
  subst r
  apply mulCheck_sound hs ?_ ha hb
  apply decide_eq_true
  have hsn : (s : Int) ≠ 0 := by exact_mod_cast hs.ne'
  constructor
  · exact Int.ediv_mul_le _ hsn
  · have h := Int.ediv_mul_le
      (-max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))) hsn
    dsimp [roundedMul,ceilDiv]
    nlinarith

/--
A list encloses all coefficients of the indicated real polynomial, including the assertion that
no unlisted coefficient is present.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Encloses` uses this definition in the
displayed construction of `Encloses`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
inductive Rep (s : Nat) : List Bounds → ℝ[X] → Prop
  /-- The empty coefficient enclosure represents the zero polynomial. -/
  | nil : Rep s [] 0
  /-- An enclosed constant coefficient followed by an enclosed tail represents C(c)+X*p. This recursive form also asserts that no unlisted coefficient remains. -/
  | cons {b : Bounds} {bs : List Bounds} {c : ℝ} {p : ℝ[X]} :
      b.Mem s c → Rep s bs p → Rep s (b::bs) (C c+X*p)

/--
Defines `add` by pattern matching with result type `List Bounds → List Bounds → List Bounds`.
The displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.add_sound` rewrites with this definition
to establish `Rep s (add as bs) (p+q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def add : List Bounds → List Bounds → List Bounds
  | [], bs => bs
  | as, [] => as
  | a::as, b::bs => addB a b :: add as bs
/--
Defines `neg` of type `List Bounds` by `as.map negB`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` uses this definition to
establish constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ,
p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def neg (as : List Bounds) : List Bounds := as.map negB
/--
Defines `trim` by pattern matching with result type `List Bounds → List Bounds`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` uses this definition to
establish constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ,
p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def trim : List Bounds → List Bounds
  | [] => []
  | a::as => let rest := trim as
    if rest.isEmpty && decide (a=zero) then [] else a::rest
/--
Defines `scale` by pattern matching with result type `List Bounds → Option (List Bounds)`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.mul_sound` uses this definition to
establish the precise assertion is `Rep s out (p*q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def scale (s : Nat) (b : Bounds) : List Bounds → Option (List Bounds)
  | [] => some []
  | a::as => do return (← mulB s b a) :: (← scale s b as)
/--
Defines `mul` by pattern matching with result type `List Bounds → List Bounds → Option (List
Bounds)`. The displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` uses this definition to
establish constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ,
p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def mul (s : Nat) : List Bounds → List Bounds → Option (List Bounds)
  | [], _ => some []
  | a::as, bs => do return add (← scale s a bs) (zero :: (← mul s as bs))
/--
Defines `range` by pattern matching with result type `List Bounds → Option Bounds`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound` uses this definition to
establish the precise assertion is `out.Mem s (p.eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def range (s : Nat) (x : Bounds) : List Bounds → Option Bounds
  | [] => some zero
  | a::as => do return addB a (← mulB s x (← range s x as))

/--
Defines `derivative` by pattern matching with result type `List Bounds → List Bounds`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.derivative_sound` uses this definition to
establish the precise assertion is `Rep s (derivative as) p.derivative`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def derivative : List Bounds → List Bounds
  | [] => []
  | _::as => add as (zero :: derivative as)

/--
Defines `exactPolynomial` by pattern matching with result type `List Int → ℝ[X]`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.exactBounds_sound` uses this definition
to establish `Rep s (exactBounds as) (exactPolynomial s as)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def exactPolynomial (s : Nat) : List Int → ℝ[X]
  | [] => 0
  | a::as => C ((a : ℝ)/s) + X * exactPolynomial s as

/--
Defines `exactBounds` of type `List Bounds` by `as.map (fun a => ⟨a,a⟩)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.exactBounds_sound` uses this definition
to establish `Rep s (exactBounds as) (exactPolynomial s as)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def exactBounds (as : List Int) : List Bounds := as.map (fun a => ⟨a,a⟩)

/--
Defines `scaleNat` of type `List Bounds` by `as.map (fun a => ⟨a.lo*n,a.hi*n⟩)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.scaleNat_sound` rewrites with this
definition to establish `Rep s (scaleNat n as) (C (n : ℝ)*p)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def scaleNat (n : Nat) (as : List Bounds) : List Bounds :=
  as.map (fun a => ⟨a.lo*n,a.hi*n⟩)

/--
The precise assertion is `Rep s (scaleNat n as) (C (n : ℝ)*p)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.inputs_sound` uses this assertion
to establish `Poly.Encloses s (inputs s piB r) (values s r)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ha`; the recursive step uses the previous-stage assertion.
-/
theorem scaleNat_sound {s n : Nat} {as : List Bounds} {p : ℝ[X]}
    (ha : Rep s as p) : Rep s (scaleNat n as) (C (n : ℝ)*p) := by
  -- Induct on `ha`; the recursive step uses the previous-stage assertion.
  induction ha with
  | nil => simpa [scaleNat] using (Rep.nil (s := s))
  | @cons a as c p hc hp ih =>
    have hn : (0 : ℝ)≤n := Nat.cast_nonneg n
    have h : (⟨a.lo*n,a.hi*n⟩ : Bounds).Mem s ((n : ℝ)*c) := by
      constructor <;> dsimp [Bounds.Mem] at * <;> push_cast
      · nlinarith [mul_le_mul_of_nonneg_right hc.1 hn]
      · nlinarith [mul_le_mul_of_nonneg_right hc.2 hn]
    have hh := Rep.cons h ih
    convert hh using 1 <;> simp only [scaleNat, List.map_cons, map_mul]
    ring

/--
The precise assertion is `Rep s (exactBounds as) (exactPolynomial s as)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.AmplitudePolynomial.Panel.actual_of_inputs`
uses this assertion to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `as`; the recursive step uses the previous-stage assertion.
-/
theorem exactBounds_sound {s : Nat} (hs : 0 < s) (as : List Int) :
    Rep s (exactBounds as) (exactPolynomial s as) := by
  induction as with
  | nil => exact Rep.nil
  | cons a as ih =>
    apply Rep.cons ?_ ih
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    simp [Bounds.Mem, mul_div_cancel₀ _ hs']

/--
The precise assertion is `Rep s (add as bs) (p+q)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.derivative_sound` uses this assertion to
establish the precise assertion is `Rep s (derivative as) p.derivative`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ha` while keeping `bs q` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem add_sound {s : Nat} {as bs : List Bounds} {p q : ℝ[X]}
    (ha : Rep s as p) (hb : Rep s bs q) : Rep s (add as bs) (p+q) := by
  -- Induct on `ha` while keeping `bs q` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ha generalizing bs q with
  | nil => simpa [add] using hb
  | @cons a as c p hc hp ih =>
    cases hb with
    | nil => simpa [add] using Rep.cons hc hp
    | @cons b bs d q hd hq =>
      have h := Rep.cons (addB_sound hc hd) (ih hq)
      convert h using 1 <;> simp only [add, map_add]
      all_goals ring

/--
The precise assertion is `Rep s (neg as) (-p)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` uses this assertion to
establish constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ,
p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ha`; the recursive step uses the previous-stage assertion.
-/
theorem neg_sound {s : Nat} {as : List Bounds} {p : ℝ[X]}
    (ha : Rep s as p) : Rep s (neg as) (-p) := by
  induction ha with
  | nil => simpa [neg] using (Rep.nil (s := s))
  | cons hc hp ih =>
    have h := Rep.cons (negB_sound hc) ih
    convert h using 1 <;> simp only [neg, List.map_cons, map_neg]
    all_goals ring

/--
The precise assertion is `Rep s (trim as) p`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` uses this assertion to
establish constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ,
p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ha`; the recursive step uses the previous-stage assertion. Separate `((trim
as).isEmpty && decide (a=zero))=true` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem trim_sound {s : Nat} (hs : 0<s) {as : List Bounds} {p : ℝ[X]}
    (ha : Rep s as p) : Rep s (trim as) p := by
  -- Induct on `ha`; the recursive step uses the previous-stage assertion.
  induction ha with
  | nil => exact Rep.nil
  | @cons a as c p hc hp ih =>
    by_cases h : ((trim as).isEmpty && decide (a=zero))=true
    · have hh : trim as=[] ∧ a=zero := by simpa only [Bool.and_eq_true,
        List.isEmpty_iff,decide_eq_true_eq] using h
      rw [hh.1] at ih
      cases ih
      have hs' : (0:ℝ)<s := by exact_mod_cast hs
      have hcz : c=0 := by rw [hh.2] at hc; dsimp [zero,Bounds.Mem] at hc; norm_num only [Int.cast_zero] at hc; nlinarith
      simpa [trim,hh.1,hh.2,hcz] using (Rep.nil (s := s))
    · simpa only [trim,ite_eq_right h] using Rep.cons hc ih

/--
The precise assertion is `Rep s out (C c*p)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.mul_sound` uses this assertion to
establish the precise assertion is `Rep s out (p*q)`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `ha` while keeping `out` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem scale_sound {s : Nat} (hs : 0 < s) {as out : List Bounds}
    {b : Bounds} {c : ℝ} {p : ℝ[X]} (hb : b.Mem s c) (ha : Rep s as p)
    (he : scale s b as = some out) : Rep s out (C c*p) := by
  -- Induct on `ha` while keeping `out` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ha generalizing out with
  | nil =>
    have h : out=[] := by simpa [scale] using he.symm
    subst out
    simpa using (Rep.nil (s := s))
  | @cons a as d p hd hp ih =>
    obtain ⟨r, hr, rest, hrest, hout⟩ : ∃ r, mulB s b a = some r ∧
        ∃ rest, scale s b as = some rest ∧ r::rest = out := by
      simpa only [scale, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] using he
    subst out
    have h := Rep.cons (mulB_sound hs hb hd hr) (ih hrest)
    convert h using 1
    simp only [map_mul]
    ring

/--
The precise assertion is `Rep s out (p*q)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` uses this assertion to
establish constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ,
p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `ha` while keeping `out` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem mul_sound {s : Nat} (hs : 0 < s) {as bs out : List Bounds}
    {p q : ℝ[X]} (ha : Rep s as p) (hb : Rep s bs q)
    (he : mul s as bs = some out) : Rep s out (p*q) := by
  -- Induct on `ha` while keeping `out` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ha generalizing out with
  | nil =>
    have h : out=[] := by simpa [mul] using he.symm
    subst out
    simpa using (Rep.nil (s := s))
  | @cons a as c p hc hp ih =>
    obtain ⟨r, hr, rest, hrest, hout⟩ : ∃ r, scale s a bs = some r ∧
        ∃ rest, mul s as bs = some rest ∧ add r (zero::rest) = out := by
      simpa only [mul, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] using he
    subst out
    have h := add_sound (scale_sound hs hc hb hr) (Rep.cons (zero_mem s) (ih hrest))
    convert h using 1
    simp only [map_zero, zero_add]
    ring

/--
The precise assertion is `out.Mem s (p.eval x)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.source_enclosed` uses this assertion to
establish the stated quantitative bound `result.Mem s (source.value (fun j => (v j).eval x))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ha` while keeping `out` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem range_sound {s : Nat} (hs : 0 < s) {as : List Bounds} {p : ℝ[X]}
    {x : ℝ} {xB out : Bounds} (ha : Rep s as p) (hx : xB.Mem s x)
    (he : range s xB as = some out) : out.Mem s (p.eval x) := by
  -- Induct on `ha` while keeping `out` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ha generalizing out with
  | nil =>
    have h : out=zero := by simpa [range] using he.symm
    subst out
    simpa using zero_mem s
  | @cons a as c p hc hp ih =>
    obtain ⟨r, hr, v, hv, hout⟩ : ∃ r, range s xB as = some r ∧
        ∃ v, mulB s xB r = some v ∧ addB a v = out := by
      simpa only [range, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] using he
    subst out
    simpa using addB_sound hc (mulB_sound hs hx (ih hr) hv)

/--
The precise assertion is `Rep s (derivative as) p.derivative`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.inputs_sound` uses this assertion
to establish `Poly.Encloses s (inputs s piB r) (values s r)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ha`; the recursive step uses the previous-stage assertion.
-/
theorem derivative_sound {s : Nat} {as : List Bounds} {p : ℝ[X]}
    (ha : Rep s as p) : Rep s (derivative as) p.derivative := by
  induction ha with
  | nil => simpa [derivative] using (Rep.nil (s := s))
  | cons hc hp ih =>
    have h := add_sound hp (Rep.cons (zero_mem s) ih)
    simpa [derivative, Polynomial.derivative_add, Polynomial.derivative_mul] using h

/--
Defines `constant` of type `Option (List Bounds)` by `(evalStep s [] [] (.literal n d)).map
(fun v => [v.1])`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.constant_sound` uses this definition to
establish the precise assertion is `Rep s out (C ((n : ℝ)/d))`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def constant (s : Nat) (n : Int) (d : Nat) : Option (List Bounds) :=
  (evalStep s [] [] (.literal n d)).map (fun v => [v.1])

/--
The precise assertion is `Rep s out (C ((n : ℝ)/d))`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` uses this assertion to
establish constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ,
p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.IntegerCertificate.evalStep_sound`
with the arguments shown in the proof.
-/
theorem constant_sound {s : Nat} (hs : 0 < s) {n : Int} {d : Nat} {out : List Bounds}
    (he : constant s n d = some out) : Rep s out (C ((n : ℝ)/d)) := by
  obtain ⟨v, hv, heq⟩ := Option.map_eq_some_iff.mp he
  subst out
  have h : v.1.Mem s ((n : ℝ)/d) :=
    evalStep_sound hs (v := fun _ => 0) (by intro i I hi; simp at hi) hv
  simpa using Rep.cons h (Rep.nil (s := s))

/--
Defines `evalOp` by pattern matching with result type `Op → Option (List Bounds)`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalOp_sound` rewrites with this
definition to construct witnesses satisfying `∃ p : ℝ[X], Rep s out p
∧ ∀ x : ℝ, p.eval x = op.value (fun i => (v i).eval x)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def evalOp (s : Nat) (stack : List (List Bounds)) : Op → Option (List Bounds)
  | .literal n d => constant s n d
  | .copy i => stack[i]?
  | .add i j => do return add (← stack[i]?) (← stack[j]?)
  | .neg i => do return neg (← stack[i]?)
  | .mul i j => do return trim (← mul s (← stack[i]?) (← stack[j]?))
  | .inv _ | .cubic _ _ => none

/--
Defines `evalProgram` by pattern matching with result type `List (List Bounds) → List Op →
Option (List (List Bounds))`. The displayed branches determine the recursive cases and their
returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalProgram_sound` uses this definition
to construct witnesses satisfying `∃ w : Nat → ℝ[X], Encloses s out w
∧ ∀ i x, (w i).eval x = codeValue (fun j => (v j).eval x) ops i`.

Article: 2610.05164v2, Section 4.1.
-/
def evalProgram (s : Nat) : List (List Bounds) → List Op → Option (List (List Bounds))
  | stack, [] => some stack
  | stack, op::ops => do evalProgram s ((← evalOp s stack op)::stack) ops

/--
Defines `Encloses` of type `Prop` by `∀ i I, stack[i]? = some I → Rep s I (v i)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalProgram_sound` uses this definition
to construct witnesses satisfying `∃ w : Nat → ℝ[X], Encloses s out w
∧ ∀ i x, (w i).eval x = codeValue (fun j => (v j).eval x) ops i`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Encloses (s : Nat) (stack : List (List Bounds)) (v : Nat → ℝ[X]) : Prop :=
  ∀ i I, stack[i]? = some I → Rep s I (v i)

/--
Polynomial operations are tied to the same scalar expression interpreter. Unsupported
non-polynomial operations are rejected, rather than approximated.

Constructs witnesses with the exact properties `∃ p : ℝ[X], Rep s out p ∧ ∀ x : ℝ, p.eval x =
op.value (fun i => (v i).eval x)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalProgram_sound` uses this identity to
establish constructs witnesses with the exact properties `∃ w : Nat → ℝ[X], Encloses s out w ∧
∀ i x, (w i).eval x = codeValue (fun j => (v j).eval x) ops i`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.constant_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.add_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.neg_sound` with the arguments shown in the
proof.
-/
theorem evalOp_sound {s : Nat} (hs : 0 < s) {stack : List (List Bounds)}
    {op : Op} {out : List Bounds} {v : Nat → ℝ[X]} (hv : Encloses s stack v)
    (he : evalOp s stack op = some out) : ∃ p : ℝ[X], Rep s out p ∧
      ∀ x : ℝ, p.eval x = op.value (fun i => (v i).eval x) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.constant_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.add_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.neg_sound` with the arguments shown in
  -- the proof.
  cases op with
  | literal n d => exact ⟨_,constant_sound hs he,by intro x; simp [Op.value]⟩
  | copy i => exact ⟨_,hv i out he,by intro x; rfl⟩
  | add i j =>
    obtain ⟨a, ha, b, hb, hout⟩ : ∃ a, stack[i]?=some a ∧
        ∃ b, stack[j]?=some b ∧ add a b=out := by
      simpa only [evalOp, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] using he
    subst out
    exact ⟨_,add_sound (hv i a ha) (hv j b hb),by intro x; simp [Op.value]⟩
  | neg i =>
    obtain ⟨a,ha,hout⟩ : ∃ a, stack[i]?=some a ∧ neg a=out := by
      simpa only [evalOp, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] using he
    subst out
    exact ⟨_,neg_sound (hv i a ha),by intro x; simp [Op.value]⟩
  | mul i j =>
    obtain ⟨a,ha,b,hb,r,hr,hout⟩ : ∃ a, stack[i]?=some a ∧
        ∃ b, stack[j]?=some b ∧ ∃ r, mul s a b=some r ∧ trim r=out := by
      simpa only [evalOp, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def,Option.some.injEq] using he
    subst out
    exact ⟨_,trim_sound hs (mul_sound hs (hv i a ha) (hv j b hb) hr),
      by intro x; simp [Op.value]⟩
  | inv i => simp [evalOp] at he
  | cubic i j => simp [evalOp] at he

/--
Constructs witnesses with the exact properties `∃ w : Nat → ℝ[X], Encloses s out w ∧ ∀ i x, (w
i).eval x = codeValue (fun j => (v j).eval x) ops i`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.source_enclosed` uses this identity to
establish the stated quantitative bound `result.Mem s (source.value (fun j => (v j).eval x))`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `ops` while keeping `stack v` arbitrary; the recursive step uses the
previous-stage assertion. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem evalProgram_sound {s : Nat} (hs : 0 < s) (ops : List Op)
    {stack out : List (List Bounds)} {v : Nat → ℝ[X]} (hv : Encloses s stack v)
    (he : evalProgram s stack ops = some out) :
    ∃ w : Nat → ℝ[X], Encloses s out w ∧ ∀ i x,
      (w i).eval x = codeValue (fun j => (v j).eval x) ops i := by
  -- Induct on `ops` while keeping `stack v` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ops generalizing stack v with
  | nil =>
    have h : stack=out := by simpa [evalProgram] using he
    subst out
    exact ⟨v,hv,by intro i x; rfl⟩
  | cons op ops ih =>
    obtain ⟨a,ha,hrest⟩ : ∃ a, evalOp s stack op=some a ∧
        evalProgram s (a::stack) ops=some out := by
      simpa only [evalProgram, Option.bind_eq_bind, Option.bind_eq_some_iff] using he
    obtain ⟨p,hp,hpval⟩ := evalOp_sound hs hv ha
    let v' : Nat → ℝ[X] := fun i => match i with | 0 => p | j+1 => v j
    have hv' : Encloses s (a::stack) v' := by
      intro i I hi
      cases i with
      | zero =>
        have h : a=I := by simpa using hi
        subst I
        exact hp
      | succ j => exact hv j I (by simpa using hi)
    obtain ⟨w,hw,hval⟩ := ih hv' hrest
    refine ⟨w,hw,?_⟩
    intro i x
    rw [hval, codeValue]
    congr 1
    funext j
    cases j with
    | zero => exact hpval x
    | succ j => rfl

/--
The stated quantitative bound `result.Mem s (source.value (fun j => (v j).eval x))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.IntegerCertificate.Poly.evalProgram_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound`,
`«2610.05164v2».Numerics.IntegerCertificate.codeExpression_value` with the arguments shown in
the proof.
-/
theorem source_enclosed {s : Nat} (hs : 0 < s) (ops : List Op)
    {stack out : List (List Bounds)} {v : Nat → ℝ[X]} (hv : Encloses s stack v)
    (he : evalProgram s stack ops = some out) {i : Nat} {source : Expr}
    (hsource : codeExpressionCheck ops i source = true) {pB : List Bounds}
    (hi : out[i]? = some pB) {x : ℝ} {xB result : Bounds} (hx : xB.Mem s x)
    (hrange : range s xB pB = some result) :
    result.Mem s (source.value (fun j => (v j).eval x)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.evalProgram_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.Poly.range_sound`,
  -- `«2610.05164v2».Numerics.IntegerCertificate.codeExpression_value` with the arguments shown
  -- in the proof.
  obtain ⟨w,hw,hval⟩ := evalProgram_sound hs ops hv he
  have h := range_sound hs (hw i pB hi) hx hrange
  have hshape : codeExpression Expr.input ops i = source := of_decide_eq_true hsource
  rw [hval] at h
  have hvalue := codeExpression_value ops Expr.input (fun j => (v j).eval x) i
  simp only [Expr.value, hshape] at hvalue
  rwa [← hvalue] at h

end «2610.05164v2».Numerics.IntegerCertificate.Poly
