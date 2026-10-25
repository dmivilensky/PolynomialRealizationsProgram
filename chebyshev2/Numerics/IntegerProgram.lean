import chebyshev2.Numerics.IntegerCubic

/-!
Article: chebyshev2, Section 4.1.
Shared arithmetic graphs, encoded as a stack of checked integer witnesses.
Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` feeds
`chebyshev2.Numerics.IntegerCertificate.evalStep_sound` (eval Step sound).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate
set_option autoImplicit false

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` rewrites with this definition
to establish `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
inductive Op where
  /-- Rational literal operation encoded by integer numerator/natural denominator. -/
  | literal (numerator : Int) (denominator : Nat)
  /-- Copy a prior stack entry using the reverse-offset addressing convention. -/
  | copy (a : Nat)
  /-- Add two prior stack values. -/
  | add (a b : Nat)
  /-- Negate a prior stack value. -/
  | neg (a : Nat)
  /-- Multiply two prior stack values. -/
  | mul (a b : Nat)
  /-- Invert a prior stack value; acceptance requires its interval excludes zero. -/
  | inv (a : Nat)
  /-- Select the positive cubic root determined by two prior coefficient values; sign and residual checks establish its enclosure. -/
  | cubic (a b : Nat)
  deriving Repr, DecidableEq

/--
One arithmetic-program node with its proposed output interval. The operation checker verifies
containment of the computed enclosure in that stored result.

Use: `chebyshev2.Numerics.IntegerCertificate.programBounds` uses this record of data and
proof obligations in the displayed construction of `programBounds`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
structure Node where
  /-- Arithmetic operation at this DAG node. -/
  op : Op
  /-- Proposed scaled output enclosure; it must contain the checker-computed enclosure. -/
  result : Bounds
  deriving Repr, DecidableEq

/--
Defines `Op.check` by pattern matching with result type `Op → Bool`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` rewrites with this definition
to establish `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Op.check (s : Nat) (stack : List Bounds) (R : Bounds) : Op → Bool
  | .literal n d => literalCheck s n d R
  | .copy a => ((stack[a]?).map (fun A => subset A R)).getD false
  | .add a b => (do return addCheck (← stack[a]?) (← stack[b]?) R).getD false
  | .neg a => ((stack[a]?).map (fun A => negCheck A R)).getD false
  | .mul a b => (do return mulCheck s (← stack[a]?) (← stack[b]?) R).getD false
  | .inv a => ((stack[a]?).map (fun A => invCheck s A R)).getD false
  | .cubic a b => (do return cubicCheck s (← stack[a]?) (← stack[b]?) R).getD false

/--
Defines `Op.value` by pattern matching with result type `Op → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this definition to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def Op.value (v : Nat → ℝ) : Op → ℝ
  | .literal n d => (n : ℝ) / d
  | .copy a => v a
  | .add a b => v a + v b
  | .neg a => -(v a)
  | .mul a b => v a * v b
  | .inv a => (v a)⁻¹
  | .cubic a b => chebyshev2.Numerics.positiveCubic (v a) (v b)

/--
Defines `Encloses` of type `Prop` by `∀ (i : Nat) (I : Bounds), stack[i]? = some I → I.Mem s (v
i)`.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.check_sound` uses this definition to
establish the precise assertion is `R.Mem s (op.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Encloses (s : Nat) (stack : List Bounds) (v : Nat → ℝ) : Prop :=
  ∀ (i : Nat) (I : Bounds), stack[i]? = some I → I.Mem s (v i)

/--
The precise assertion is `R.Mem s (op.value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.programCheck_sound` uses this assertion to
establish the precise assertion is `Encloses s (programBounds stack nodes) (programValue v
nodes)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.literalCheck_sound`,
`chebyshev2.Numerics.IntegerCertificate.subset_sound`,
`chebyshev2.Numerics.IntegerCertificate.addCheck_sound` with the arguments shown in the
proof.
-/
theorem Op.check_sound (op : Op) {s : Nat} (hs : 0 < s)
    {stack : List Bounds} {R : Bounds} {v : Nat → ℝ}
    (hv : Encloses s stack v) (hc : op.check s stack R = true) :
    R.Mem s (op.value v) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.literalCheck_sound`,
  -- `chebyshev2.Numerics.IntegerCertificate.subset_sound`,
  -- `chebyshev2.Numerics.IntegerCertificate.addCheck_sound` with the arguments shown in
  -- the proof.
  cases op with
  | literal n d => exact literalCheck_sound hc
  | copy a =>
    cases ha : stack[a]? with
    | none => simp [Op.check, ha] at hc
    | some A => exact subset_sound (by simpa [Op.check, ha] using hc) (hv a A ha)
  | neg a =>
    cases ha : stack[a]? with
    | none => simp [Op.check, ha] at hc
    | some A => exact negCheck_sound (by simpa [Op.check, ha] using hc) (hv a A ha)
  | inv a =>
    cases ha : stack[a]? with
    | none => simp [Op.check, ha] at hc
    | some A => exact invCheck_sound hs (by simpa [Op.check, ha] using hc) (hv a A ha)
  | add a b =>
    cases ha : stack[a]? with
    | none => simp [Op.check, ha] at hc
    | some A =>
      cases hb : stack[b]? with
      | none => simp [Op.check, ha, hb] at hc
      | some B => exact addCheck_sound (by simpa [Op.check, ha, hb] using hc) (hv a A ha) (hv b B hb)
  | mul a b =>
    cases ha : stack[a]? with
    | none => simp [Op.check, ha] at hc
    | some A =>
      cases hb : stack[b]? with
      | none => simp [Op.check, ha, hb] at hc
      | some B => exact mulCheck_sound hs (by simpa [Op.check, ha, hb] using hc) (hv a A ha) (hv b B hb)
  | cubic a b =>
    cases ha : stack[a]? with
    | none => simp [Op.check, ha] at hc
    | some A =>
      cases hb : stack[b]? with
      | none => simp [Op.check, ha, hb] at hc
      | some B => exact cubicCheck_sound hs (by simpa [Op.check, ha, hb] using hc) (hv a A ha) (hv b B hb)

/--
Defines `programCheck` by pattern matching with result type `List Bounds → List Node → Bool`.
The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.programCheck_sound` uses this definition to
establish the precise assertion is `Encloses s (programBounds stack nodes) (programValue v
nodes)`.

Article: chebyshev2, Section 4.1.
-/
def programCheck (s : Nat) : List Bounds → List Node → Bool
  | _, [] => true
  | stack, node :: nodes => node.op.check s stack node.result &&
      programCheck s (node.result :: stack) nodes

/--
Defines `programBounds` by pattern matching with result type `List Bounds → List Node → List
Bounds`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.programNegativeCheck` uses this definition in
the displayed construction of `programNegativeCheck`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
def programBounds : List Bounds → List Node → List Bounds
  | stack, [] => stack
  | stack, node :: nodes => programBounds (node.result :: stack) nodes

/--
Defines `programValue` by pattern matching with result type `(Nat → ℝ) → List Node → (Nat →
ℝ)`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.programCheck_sound` uses this definition to
establish the precise assertion is `Encloses s (programBounds stack nodes) (programValue v
nodes)`.

Article: chebyshev2, Section 4.1.
-/
noncomputable def programValue : (Nat → ℝ) → List Node → (Nat → ℝ)
  | v, [] => v
  | v, node :: nodes => programValue (fun i => match i with
      | 0 => node.op.value v
      | j+1 => v j) nodes

/--
The precise assertion is `Encloses s (programBounds stack nodes) (programValue v nodes)`.

Use: `chebyshev2.Numerics.IntegerCertificate.programNegativeCheck_sound` uses this
assertion to prove the bound `programValue v nodes 0 < 0`.

Article: chebyshev2, Section 4.1.

Proof: Induct on `nodes` while keeping `stack v` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem programCheck_sound {s : Nat} (hs : 0 < s) (nodes : List Node)
    {stack : List Bounds} {v : Nat → ℝ} (hv : Encloses s stack v)
    (hc : programCheck s stack nodes = true) :
    Encloses s (programBounds stack nodes) (programValue v nodes) := by
  -- Induct on `nodes` while keeping `stack v` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction nodes generalizing stack v with
  | nil => exact hv
  | cons node nodes ih =>
    have hh : node.op.check s stack node.result = true ∧
        programCheck s (node.result :: stack) nodes = true := by
      simpa only [programCheck, Bool.and_eq_true] using hc
    apply ih _ hh.2
    intro i I hi
    cases i with
    | zero =>
      have he : node.result = I := by simpa using hi
      subst I
      exact node.op.check_sound hs hv hh.1
    | succ j => exact hv j I (by simpa using hi)

/--
Defines `programNegativeCheck` of type `Bool` by `programCheck s stack nodes &&
(((programBounds stack nodes)[0]?).map negative).getD false`.

Use: `chebyshev2.Numerics.IntegerCertificate.programNegativeCheck_sound` uses this
definition to prove the bound `programValue v nodes 0 < 0`.

Article: chebyshev2, Section 4.1.
-/
def programNegativeCheck (s : Nat) (stack : List Bounds) (nodes : List Node) : Bool :=
  programCheck s stack nodes &&
    (((programBounds stack nodes)[0]?).map negative).getD false

/--
The stated quantitative bound `programValue v nodes 0 < 0`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.negative_sound`,
`chebyshev2.Numerics.IntegerCertificate.programCheck_sound` with the arguments shown in the
proof.
-/
theorem programNegativeCheck_sound {s : Nat} (hs : 0 < s) (nodes : List Node)
    {stack : List Bounds} {v : Nat → ℝ} (hv : Encloses s stack v)
    (hc : programNegativeCheck s stack nodes = true) : programValue v nodes 0 < 0 := by
  -- Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.negative_sound`,
  -- `chebyshev2.Numerics.IntegerCertificate.programCheck_sound` with the arguments shown
  -- in the proof.
  have hh : programCheck s stack nodes = true ∧
      (((programBounds stack nodes)[0]?).map negative).getD false = true := by
    simpa only [programNegativeCheck, Bool.and_eq_true] using hc
  cases hi : (programBounds stack nodes)[0]? with
  | none => simp [hi] at hh
  | some I =>
    exact negative_sound hs (by simpa [hi] using hh.2)
      (programCheck_sound hs nodes hv hh.1 0 I hi)

end chebyshev2.Numerics.IntegerCertificate
