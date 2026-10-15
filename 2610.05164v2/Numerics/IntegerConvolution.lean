import «2610.05164v2».Numerics.IntegerPolynomial

/-!
Article: 2610.05164v2, Section 4.1.
Interval convolution with one outward division per output coefficient.
Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.convolution_sound` feeds
`«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalOp_sound` (eval Op sound).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.IntegerCertificate.Poly
open Polynomial LeanCert.Core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `rawMul` of type `Bounds` by `⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo)
(a.hi*b.hi)), max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.rawMul_sound` uses this definition to
establish the precise assertion is `(rawMul a b).Mem (s*s) (x*y)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rawMul (a b : Bounds) : Bounds :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
    max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
/--
Defines `rawScale` of type `List Bounds` by `bs.map (rawMul a)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.rawScale_sound` rewrites with this
definition to establish `Rep (s*s) (rawScale a bs) (C c*p)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rawScale (a : Bounds) (bs : List Bounds) : List Bounds := bs.map (rawMul a)
/--
Defines `rawProduct` by pattern matching with result type `List Bounds → List Bounds → List
Bounds`. The displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.convolution` uses this definition in the
displayed construction of `convolution`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rawProduct : List Bounds → List Bounds → List Bounds
  | [], _ => []
  | a::as, bs => add (rawScale a bs) (zero::rawProduct as bs)
/--
Defines `roundScale` of type `Bounds` by `⟨a.lo/s,ceilDiv a.hi s⟩`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.convolution` uses this definition in the
displayed construction of `convolution`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def roundScale (s : Nat) (a : Bounds) : Bounds := ⟨a.lo/s,ceilDiv a.hi s⟩
/--
Defines `convolution` of type `List Bounds` by `(rawProduct as bs).map (roundScale s)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.convolution_sound` uses this definition
to establish `Rep s (convolution s as bs) (p*q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def convolution (s : Nat) (as bs : List Bounds) : List Bounds :=
  (rawProduct as bs).map (roundScale s)

/--
The precise assertion is `(rawMul a b).Mem (s*s) (x*y)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.rawScale_sound` uses this assertion to
establish the precise assertion is `Rep (s*s) (rawScale a bs) (C c*p)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem rawMul_sound {s : Nat} {a b : Bounds} {x y : ℝ}
    (ha : a.Mem s x) (hb : b.Mem s y) : (rawMul a b).Mem (s*s) (x*y) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hal : a.lo≤a.hi := by exact_mod_cast ha.1.trans ha.2
  have hbl : b.lo≤b.hi := by exact_mod_cast hb.1.trans hb.2
  let A : IntervalRat := ⟨a.lo,a.hi,by exact_mod_cast hal⟩
  let B : IntervalRat := ⟨b.lo,b.hi,by exact_mod_cast hbl⟩
  have hh := IntervalRat.mem_mul
    (show (s:ℝ)*x∈A by simpa [A,IntervalRat.mem_def,Bounds.Mem] using ha)
    (show (s:ℝ)*y∈B by simpa [B,IntervalRat.mem_def,Bounds.Mem] using hb)
  simp only [IntervalRat.mem_def,IntervalRat.mul,IntervalRat.min4,IntervalRat.max4,
    A,B,Rat.cast_min,Rat.cast_max,Rat.cast_mul,Rat.cast_intCast] at hh
  simpa only [rawMul,Bounds.Mem,Int.cast_min,Int.cast_max,Int.cast_mul,Nat.cast_mul,
    mul_assoc,mul_left_comm,mul_comm] using hh

/--
The precise assertion is `Rep (s*s) (rawScale a bs) (C c*p)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.rawProduct_sound` uses this assertion to
establish the precise assertion is `Rep (s*s) (rawProduct as bs) (p*q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `hb`; the recursive step uses the previous-stage assertion.
-/
theorem rawScale_sound {s : Nat} {a : Bounds} {bs : List Bounds} {c : ℝ} {p : ℝ[X]}
    (ha : a.Mem s c) (hb : Rep s bs p) : Rep (s*s) (rawScale a bs) (C c*p) := by
  induction hb with
  | nil => simpa [rawScale] using (Rep.nil (s := s*s))
  | cons hc hp ih =>
    have h := Rep.cons (rawMul_sound ha hc) ih
    convert h using 1 <;> simp only [rawScale,List.map_cons,map_mul]
    ring

/--
The precise assertion is `Rep (s*s) (rawProduct as bs) (p*q)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.convolution_sound` uses this assertion to
establish the precise assertion is `Rep s (convolution s as bs) (p*q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ha`; the recursive step uses the previous-stage assertion.
-/
theorem rawProduct_sound {s : Nat} {as bs : List Bounds} {p q : ℝ[X]}
    (ha : Rep s as p) (hb : Rep s bs q) : Rep (s*s) (rawProduct as bs) (p*q) := by
  induction ha with
  | nil => simpa [rawProduct] using (Rep.nil (s := s*s))
  | cons hc hp ih =>
    have h := add_sound (rawScale_sound hc hb) (Rep.cons (zero_mem (s*s)) ih)
    convert h using 1 <;> simp only [rawProduct,map_zero,zero_add]
    ring

/--
The precise assertion is `(roundScale s a).Mem s x`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.convolution_sound` uses this assertion to
establish the precise assertion is `Rep s (convolution s as bs) (p*q)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem roundScale_sound {s : Nat} (hs : 0<s) {a : Bounds} {x : ℝ}
    (ha : a.Mem (s*s) x) : (roundScale s a).Mem s x := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hsn : (s:Int)≠0 := by exact_mod_cast hs.ne'
  have hl : ((a.lo/(s:Int):Int):ℝ)*s≤(a.lo:ℝ) := by exact_mod_cast Int.ediv_mul_le a.lo hsn
  have hu : (a.hi:ℝ)≤((ceilDiv a.hi s:Int):ℝ)*s := by
    have hh := Int.ediv_mul_le (-a.hi) hsn
    have hh' : a.hi≤ceilDiv a.hi s*(s:Int) := by dsimp [ceilDiv]; nlinarith
    exact_mod_cast hh'
  have hl' := hl.trans ha.1
  have hu' := ha.2.trans hu
  dsimp [Bounds.Mem,roundScale] at *
  push_cast at hl' hu'
  constructor
  · apply (mul_le_mul_iff_right₀ hs').mp
    nlinarith [hl']
  · apply (mul_le_mul_iff_right₀ hs').mp
    nlinarith [hu']

/--
The precise assertion is `Rep s (convolution s as bs) (p*q)`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.Poly.Taylor.evalOp_sound` uses this assertion
to establish `At s out x (op.value v)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `hc`; the recursive step uses the previous-stage assertion.
-/
theorem convolution_sound {s : Nat} (hs : 0<s) {as bs : List Bounds} {p q : ℝ[X]}
    (ha : Rep s as p) (hb : Rep s bs q) : Rep s (convolution s as bs) (p*q) := by
  have roundRep {cs : List Bounds} {f : ℝ[X]} (hc : Rep (s*s) cs f) :
      Rep s (cs.map (roundScale s)) f := by
    induction hc with
    | nil => exact Rep.nil
    | cons hc hp ih => exact Rep.cons (roundScale_sound hs hc) ih
  exact roundRep (rawProduct_sound ha hb)

end «2610.05164v2».Numerics.IntegerCertificate.Poly
