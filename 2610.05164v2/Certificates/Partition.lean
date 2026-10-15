import «2610.05164v2».Certificates.ExactNumbers
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Article: 2610.05164v2, Section 4.1.
Exact ordered partitions and their closed-interval coverage.
Use: `«2610.05164v2».Certificates.PartitionFrom.le` feeds
`«2610.05164v2».Numerics.IntegerCertificate.Poly.integral_error_cover` (integral error cover).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Certificates
open Set
set_option autoImplicit false

/--
Decoded rational partition data, with the stated endpoint and adjacency/coverage predicate
required where it appears. Parsing a cell list and proving its coverage are explicit separate
obligations.

Use: `«2610.05164v2».Certificates.PartitionFrom.cover_or_left` uses this record of data and
proof obligations to establish the identity `x=(a:ℝ) ∨ ∃ c∈cs,c.contains x`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure Cell where
  /-- Lower endpoint of the complete rational partition. -/
  lo : ℚ
  /-- Upper endpoint of the complete rational partition. -/
  hi : ℚ
  deriving DecidableEq, Repr

/--
Defines `Cell.contains` of type `Prop` by `(c.lo:ℝ)≤x ∧ x≤(c.hi:ℝ)`.

Use: `«2610.05164v2».Certificates.PartitionFrom.cover_or_left` uses this definition to
establish exact identity `x=(a:ℝ) ∨ ∃ c∈cs,c.contains x`.

Article: 2610.05164v2, Section 4.1.
-/
def Cell.contains (c : Cell) (x : ℝ) : Prop := (c.lo:ℝ)≤x ∧ x≤(c.hi:ℝ)

/--
Defines `PartitionFrom` by pattern matching with result type `List Cell → Prop`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Certificates.BlockChain.partition` uses this definition to establish the
precise assertion is `PartitionFrom a b (bs.flatMap PartitionBlock.cells)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def PartitionFrom (a b : ℚ) : List Cell → Prop
  | [] => a=b
  | c::cs => c.lo=a ∧ c.lo<c.hi ∧ PartitionFrom c.hi b cs

/--
Supplies the typeclass structure specified by `Decidable (PartitionFrom a b cs)`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `cs` while keeping `a` arbitrary; the recursive step uses the previous-stage
assertion.
-/
instance (a b : ℚ) (cs : List Cell) : Decidable (PartitionFrom a b cs) := by
  induction cs generalizing a with
  | nil => exact inferInstanceAs (Decidable (a=b))
  | cons c cs ih => exact inferInstanceAs (Decidable (c.lo=a ∧ c.lo<c.hi ∧ PartitionFrom c.hi b cs))

 /--
Exact identity `x=(a:ℝ) ∨ ∃ c∈cs,c.contains x`.

Use: `«2610.05164v2».Certificates.PartitionFrom.cover` uses this identity to establish
constructs witnesses with the exact properties `∃ c∈cs,c.contains x`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `cs` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion. Separate `x≤(c.hi:ℝ)` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem PartitionFrom.cover_or_left {a b : ℚ} {cs : List Cell}
    (h : PartitionFrom a b cs) {x : ℝ} (hx : x∈Icc (a:ℝ) b) :
    x=(a:ℝ) ∨ ∃ c∈cs,c.contains x := by
  -- Induct on `cs` while keeping `a` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing a with
  | nil =>
    change a=b at h
    subst b
    exact Or.inl (le_antisymm hx.2 hx.1)
  | cons c cs ih =>
    rcases h with ⟨hlo,_,htail⟩
    by_cases htop : x≤(c.hi:ℝ)
    · exact Or.inr ⟨c,List.mem_cons_self,by simpa only [Cell.contains,hlo] using And.intro hx.1 htop⟩
    · have hi : (c.hi:ℝ)<x := lt_of_not_ge htop
      rcases ih htail ⟨hi.le,hx.2⟩ with he | ⟨d,hd,hx⟩
      · exact False.elim (hi.ne' he)
      · exact Or.inr ⟨d,List.mem_cons_of_mem _ hd,hx⟩

 /--
Constructs witnesses with the exact properties `∃ c∈cs,c.contains x`.

Use: `«2610.05164v2».Numerics.actualJetCover_sound` uses this assertion to establish
establishes the uniform, quantified assertion `∀ x∈Icc (a:ℝ) b,∃ c∈cells,x∈Icc (c.domain.lo:ℝ)
c.domain.hi ∧ JetEncloses c.jet f (Icc (c.domain.lo:ℝ) c.domain.hi) x n`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Certificates.PartitionFrom.cover_or_left`
with the arguments shown in the proof.
-/
theorem PartitionFrom.cover {a b : ℚ} {cs : List Cell}
    (h : PartitionFrom a b cs) (hab : a<b) {x : ℝ} (hx : x∈Icc (a:ℝ) b) :
    ∃ c∈cs,c.contains x := by
  -- Use the identities/estimates `«2610.05164v2».Certificates.PartitionFrom.cover_or_left`
  -- with the arguments shown in the proof.
  rcases h.cover_or_left hx with he | he
  · cases cs with
    | nil => exact False.elim (hab.ne h)
    | cons c cs =>
      exact ⟨c,List.mem_cons_self,by
        rcases h with ⟨hlo,hlt,_⟩
        constructor
        · simpa only [he,hlo] using le_refl (a:ℝ)
        · rw [he,← hlo]
          exact_mod_cast hlt.le⟩
  · exact he

 /--
Defines `cellsOfNumbers` by pattern matching with result type `List ℚ → Option (List Cell)`.
The displayed branches determine the recursive cases and their returned values.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.
-/
def cellsOfNumbers : List ℚ → Option (List Cell)
  | [] => some []
  | a::b::rest => (cellsOfNumbers rest).map (Cell.mk a b :: ·)
  | [_] => none

 /--
The precise assertion is `PartitionFrom a c (xs++ys)`.

Use: `«2610.05164v2».Certificates.BlockChain.partition` uses this assertion to establish the
precise assertion is `PartitionFrom a b (bs.flatMap PartitionBlock.cells)`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `xs` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem PartitionFrom.append {a b c : ℚ} {xs ys : List Cell}
    (hx : PartitionFrom a b xs) (hy : PartitionFrom b c ys) :
    PartitionFrom a c (xs++ys) := by
  induction xs generalizing a with
  | nil => change a=b at hx;subst b;exact hy
  | cons x xs ih => exact ⟨hx.1,hx.2.1,ih hx.2.2⟩

/--
Decoded rational partition data, with the stated endpoint and adjacency/coverage predicate
required where it appears. Parsing a cell list and proving its coverage are explicit separate
obligations.

Use: `«2610.05164v2».Certificates.BlockChain.partition` uses this record of data and proof
obligations to establish `PartitionFrom a b (bs.flatMap
PartitionBlock.cells)`.

Article: 2610.05164v2, Section 4.1.
-/
structure PartitionBlock extends DecodedBytes where
  /-- Ordered cells decoded from the exact numerical input. -/
  cells : List Cell
  /-- The input numbers decode to exactly this cell list. -/
  parsed : cellsOfNumbers values=some cells
  /-- Lower endpoint of the complete rational partition. -/
  lo : ℚ
  /-- Upper endpoint of the complete rational partition. -/
  hi : ℚ
  /-- Coverage/adjacency predicate ensuring that the cell list partitions the full endpoint interval. -/
  partition : PartitionFrom lo hi cells

 /--
Defines `BlockChain` by pattern matching with result type `List PartitionBlock → Prop`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Certificates.BlockChain.partition` uses this definition to establish the
precise assertion is `PartitionFrom a b (bs.flatMap PartitionBlock.cells)`.

Article: 2610.05164v2, Section 4.1.
-/
def BlockChain (a b : ℚ) : List PartitionBlock → Prop
  | [] => a=b
  | c::cs => c.lo=a ∧ BlockChain c.hi b cs

/--
Supplies the typeclass structure specified by `Decidable (BlockChain a b cs)`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `cs` while keeping `a` arbitrary; the recursive step uses the previous-stage
assertion.
-/
instance (a b : ℚ) (cs : List PartitionBlock) : Decidable (BlockChain a b cs) := by
  induction cs generalizing a with
  | nil => exact inferInstanceAs (Decidable (a=b))
  | cons c cs ih => exact inferInstanceAs (Decidable (c.lo=a ∧ BlockChain c.hi b cs))

 /--
The precise assertion is `PartitionFrom a b (bs.flatMap PartitionBlock.cells)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `bs` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem BlockChain.partition {a b : ℚ} {bs : List PartitionBlock} (h : BlockChain a b bs) :
    PartitionFrom a b (bs.flatMap PartitionBlock.cells) := by
  induction bs generalizing a with
  | nil => exact h
  | cons c cs ih =>
    change PartitionFrom a b (c.cells++cs.flatMap PartitionBlock.cells)
    rw [← h.1]
    exact c.partition.append (ih h.2)

/--
The stated quantitative bound `a≤b`.

Use: `«2610.05164v2».Certificates.PartitionFrom.bounds` uses this bound to establish
establishes the uniform, quantified assertion `∀ c∈cs,a≤c.lo ∧ c.lo<c.hi ∧ c.hi≤b`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `cs` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem PartitionFrom.le {a b : ℚ} {cs : List Cell} (h : PartitionFrom a b cs) : a≤b := by
  induction cs generalizing a with
  | nil => change a=b at h;exact h.le
  | cons c cs ih => exact h.1 ▸ h.2.1.le.trans (ih h.2.2)

/--
Establishes the uniform, quantified assertion `∀ c∈cs,a≤c.lo ∧ c.lo<c.hi ∧ c.hi≤b`.

Use: `«2610.05164v2».Certificates.PartitionFrom.pairwise` uses this bound to establish the
stated quantitative bound `cs.Pairwise (fun c d => c.hi≤d.lo)`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `cs` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem PartitionFrom.bounds {a b : ℚ} {cs : List Cell} (h : PartitionFrom a b cs) :
    ∀ c∈cs,a≤c.lo ∧ c.lo<c.hi ∧ c.hi≤b := by
  -- Induct on `cs` while keeping `a` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cs generalizing a with
  | nil => simp
  | cons d ds ih =>
    intro c hc
    rcases List.mem_cons.mp hc with he | hc
    · subst c
      exact ⟨h.1.ge,h.2.1,h.2.2.le⟩
    · have hb := ih h.2.2 c hc
      exact ⟨(h.1 ▸ h.2.1.le).trans hb.1,hb.2⟩

/--
The stated quantitative bound `cs.Pairwise (fun c d => c.hi≤d.lo)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `cs` while keeping `a` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem PartitionFrom.pairwise {a b : ℚ} {cs : List Cell} (h : PartitionFrom a b cs) :
    cs.Pairwise (fun c d => c.hi≤d.lo) := by
  induction cs generalizing a with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
    apply List.pairwise_cons.mpr
    exact ⟨fun d hd => (h.2.2.bounds d hd).1,ih h.2.2⟩


end «2610.05164v2».Certificates
