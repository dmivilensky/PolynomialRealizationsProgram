import chebyshev2.Numerics.IntegerProgram

/-!
Article: chebyshev2, Section 4.1.
An independent source expression for a shared arithmetic graph.
Use: `chebyshev2.Numerics.IntegerCertificate.codeExpressionCheck` feeds
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.check_sound` (The complete local acceptance
theorem: all numerical premises are discharged by the executable certificate predicate).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate
set_option autoImplicit false

/--
Defines `rationalIntervalCheck` of type `Bool` by `literalCheck s a.num a.den I && literalCheck
s b.num b.den I`.

Use: `chebyshev2.Numerics.IntegerCertificate.rationalIntervalCheck_sound` uses this
definition to establish `I.Mem s x`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rationalIntervalCheck (s : Nat) (a b : ℚ) (I : Bounds) : Bool :=
  literalCheck s a.num a.den I && literalCheck s b.num b.den I

/--
The precise assertion is `I.Mem s x`.

Use: `chebyshev2.Certificates.Compact.ContactValues.ValidPanel.actual` uses this assertion
to establish `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.literalCheck_sound` with the arguments shown in the
proof.
-/
theorem rationalIntervalCheck_sound {s : Nat} (hs : 0 < s) {a b : ℚ}
    {I : Bounds} (hc : rationalIntervalCheck s a b I = true)
    {x : ℝ} (hl : (a : ℝ) ≤ x) (hu : x ≤ (b : ℝ)) : I.Mem s x := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.literalCheck_sound` with the arguments shown
  -- in the proof.
  have hh : literalCheck s a.num a.den I = true ∧
      literalCheck s b.num b.den I = true := by simpa [rationalIntervalCheck] using hc
  have ha : I.Mem s (a : ℝ) := by
    simpa only [Rat.cast_def] using literalCheck_sound hh.1
  have hb : I.Mem s (b : ℝ) := by
    simpa only [Rat.cast_def] using literalCheck_sound hh.2
  have hsr : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hl hsr),
    (mul_le_mul_of_nonneg_left hu hsr).trans hb.2⟩

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `chebyshev2.Numerics.IntegerCertificate.expressionCheck` uses this definition in the
displayed construction of `expressionCheck`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
inductive Expr where
  /-- One actual real input selected by index. -/
  | input (i : Nat)
  /-- The exact real value of an integer numerator divided by a natural denominator. -/
  | literal (n : Int) (d : Nat)
  /-- Addition of two real expression values. -/
  | add (a b : Expr)
  /-- Negation of a real expression value. -/
  | neg (a : Expr)
  /-- Multiplication of two real expression values. -/
  | mul (a b : Expr)
  /-- Reciprocal of an expression; checker acceptance separately excludes a zero denominator. -/
  | inv (a : Expr)
  /-- The selected positive root of z³-a*z-b=0, with coefficient signs required by checker soundness. -/
  | cubic (a b : Expr)
  deriving Repr, DecidableEq

/--
Defines `Expr.value` by pattern matching with result type `Expr → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.expression_value` uses this definition to
establish exact identity `(op.expression E).value v = op.value (fun i => (E i).value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def Expr.value (v : Nat → ℝ) : Expr → ℝ
  | .input i => v i
  | .literal n d => (n : ℝ) / d
  | .add a b => a.value v + b.value v
  | .neg a => -(a.value v)
  | .mul a b => a.value v * b.value v
  | .inv a => (a.value v)⁻¹
  | .cubic a b => positiveCubic (a.value v) (b.value v)

/--
Defines `Op.expression` by pattern matching with result type `Op → Expr`. The displayed
branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.Op.expression_value` uses this definition to
establish exact identity `(op.expression E).value v = op.value (fun i => (E i).value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def Op.expression (v : Nat → Expr) : Op → Expr
  | .literal n d => .literal n d
  | .copy a => v a
  | .add a b => .add (v a) (v b)
  | .neg a => .neg (v a)
  | .mul a b => .mul (v a) (v b)
  | .inv a => .inv (v a)
  | .cubic a b => .cubic (v a) (v b)

/--
Exact identity `(op.expression E).value v = op.value (fun i => (E i).value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.programExpression_value` uses this identity to
establish exact identity `(programExpression E nodes i).value v = programValue (fun j => (E
j).value v) nodes i`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem Op.expression_value (op : Op) (E : Nat → Expr) (v : Nat → ℝ) :
    (op.expression E).value v = op.value (fun i => (E i).value v) := by cases op <;> rfl

/--
Defines `programExpression` by pattern matching with result type `(Nat → Expr) → List Node →
(Nat → Expr)`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.expressionCheck` uses this definition in the
displayed construction of `expressionCheck`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Section 4.1.
-/
def programExpression : (Nat → Expr) → List Node → (Nat → Expr)
  | E, [] => E
  | E, node :: nodes => programExpression (fun i => match i with
      | 0 => node.op.expression E
      | j+1 => E j) nodes

/--
Exact identity `(programExpression E nodes i).value v = programValue (fun j => (E j).value v)
nodes i`.

Use: `chebyshev2.Numerics.IntegerCertificate.source_enclosed` rewrites with this identity
to establish `I.Mem s (source.value v)`.

Article: chebyshev2, Section 4.1.

Proof: Induct on `nodes` while keeping `E` arbitrary; the recursive step uses the
previous-stage assertion. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem programExpression_value (nodes : List Node) (E : Nat → Expr) (v : Nat → ℝ)
    (i : Nat) : (programExpression E nodes i).value v =
      programValue (fun j => (E j).value v) nodes i := by
  -- Induct on `nodes` while keeping `E` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction nodes generalizing E with
  | nil => rfl
  | cons node nodes ih =>
    rw [programExpression, ih, programValue]
    congr 1
    funext j
    cases j with
    | zero => exact node.op.expression_value E v
    | succ j => rfl

/--
Defines `expressionCheck` of type `Bool` by `decide (programExpression Expr.input nodes i =
source)`.

Use: `chebyshev2.Numerics.IntegerCertificate.expressionCheck_of_code` uses this definition
to establish acceptance/decoding identity for the displayed finite data: `expressionCheck
(annotate ops bounds) i source = true`.

Article: chebyshev2, Section 4.1.
-/
def expressionCheck (nodes : List Node) (i : Nat) (source : Expr) : Bool :=
  decide (programExpression Expr.input nodes i = source)

/--
Defines `codeExpression` by pattern matching with result type `(Nat → Expr) → List Op → (Nat →
Expr)`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.codeExpressionCheck` uses this definition in
the displayed construction of `codeExpressionCheck`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def codeExpression : (Nat → Expr) → List Op → (Nat → Expr)
  | E, [] => E
  | E, op :: ops => codeExpression (fun i => match i with
      | 0 => op.expression E
      | j+1 => E j) ops

/--
Exact identity `programExpression E nodes = codeExpression E (nodes.map Node.op)`.

Use: `chebyshev2.Numerics.IntegerCertificate.expressionCheck_of_code` uses this identity to
establish acceptance/decoding identity for the displayed finite data: `expressionCheck
(annotate ops bounds) i source = true`.

Article: chebyshev2, Section 4.1.

Proof: Induct on `nodes` while keeping `E` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem programExpression_eq_code (nodes : List Node) (E : Nat → Expr) :
    programExpression E nodes = codeExpression E (nodes.map Node.op) := by
  induction nodes generalizing E with
  | nil => rfl
  | cons node nodes ih => exact ih _

/--
One shared operation list, many independent interval annotations.

Use: `chebyshev2.Numerics.IntegerCertificate.annotate_ops` rewrites with this definition to
establish exact identity `(annotate ops bounds).map Node.op = ops`.

Article: chebyshev2, Section 4.1.
-/
def annotate (ops : List Op) (bounds : List Bounds) : List Node :=
  List.zipWith Node.mk ops bounds

/--
Exact identity `(annotate ops bounds).map Node.op = ops`.

Use: `chebyshev2.Numerics.IntegerCertificate.expressionCheck_of_code` uses this identity to
establish acceptance/decoding identity for the displayed finite data: `expressionCheck
(annotate ops bounds) i source = true`.

Article: chebyshev2, Section 4.1.

Proof: Induct on `ops` while keeping `bounds` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem annotate_ops (ops : List Op) (bounds : List Bounds) (h : bounds.length = ops.length) :
    (annotate ops bounds).map Node.op = ops := by
  -- Induct on `ops` while keeping `bounds` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ops generalizing bounds with
  | nil => simp [annotate]
  | cons op ops ih =>
    cases bounds with
    | nil => simp at h
    | cons I bounds =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simpa [annotate] using congrArg (List.cons op) (ih bounds h)

/--
Defines `codeExpressionCheck` of type `Bool` by `decide (codeExpression Expr.input ops i =
source)`.

Use: `chebyshev2.Numerics.IntegerCertificate.expressionCheck_of_code` uses this definition
to establish acceptance/decoding identity for the displayed finite data: `expressionCheck
(annotate ops bounds) i source = true`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def codeExpressionCheck (ops : List Op) (i : Nat) (source : Expr) : Bool :=
  decide (codeExpression Expr.input ops i = source)

/--
Acceptance/decoding identity for the displayed finite data: `expressionCheck (annotate ops
bounds) i source = true`.

Use: `chebyshev2.Numerics.IntegerCertificate.rows_source_enclosed` uses this identity to
establish the precise assertion is `I.Mem s (source.value v)`.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.programExpression_eq_code`,
`chebyshev2.Numerics.IntegerCertificate.annotate_ops` with the arguments shown in the
proof.
-/
theorem expressionCheck_of_code {ops : List Op} {bounds : List Bounds}
    (hl : bounds.length = ops.length) {i : Nat} {source : Expr}
    (hc : codeExpressionCheck ops i source = true) :
    expressionCheck (annotate ops bounds) i source = true := by
  simpa only [expressionCheck, codeExpressionCheck, programExpression_eq_code, annotate_ops ops bounds hl]
    using hc

/--
Encloses the independently defined source expression, including its exact literal constants. No
real-function identity is delegated to a generator.

The precise assertion is `I.Mem s (source.value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.rows_source_enclosed` uses this assertion to
establish the precise assertion is `I.Mem s (source.value v)`.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.programExpression_value`,
`chebyshev2.Numerics.IntegerCertificate.programCheck_sound` with the arguments shown in the
proof.
-/
theorem source_enclosed {s : Nat} (hs : 0 < s) (nodes : List Node)
    {stack : List Bounds} {v : Nat → ℝ} (hv : Encloses s stack v)
    (hc : programCheck s stack nodes = true) {i : Nat} {source : Expr}
    (he : expressionCheck nodes i source = true) {I : Bounds}
    (hi : (programBounds stack nodes)[i]? = some I) :
    I.Mem s (source.value v) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.programExpression_value`,
  -- `chebyshev2.Numerics.IntegerCertificate.programCheck_sound` with the arguments shown
  -- in the proof.
  have hsource : programExpression Expr.input nodes i = source := of_decide_eq_true he
  rw [← hsource, programExpression_value]
  exact programCheck_sound hs nodes hv hc i I hi

end chebyshev2.Numerics.IntegerCertificate
