import chebyshev2.Numerics.IntegerCover

/-!
Article: chebyshev2, Section 4.1.
Computed integer intervals: intermediate annotations need not be stored.
Use: `chebyshev2.Numerics.IntegerCertificate.codeExpression_value` feeds
`chebyshev2.Numerics.IntegerCertificate.Poly.Taylor.source_enclosed` (source enclosed).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate
set_option autoImplicit false

/--
Defines `ceilDiv` of type `Int` by `-((-n)/d)`.

Use: `chebyshev2.Numerics.IntegerCertificate.proposeOp` uses this definition in the
displayed construction of `proposeOp`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def ceilDiv (n d : Int) : Int := -((-n)/d)

/--
Defines `proposeOp` by pattern matching with result type `Op → Option (Bounds × List Bounds)`.
The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.evalStep` uses this definition in the
displayed construction of `evalStep`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def proposeOp (s : Nat) (stack witnesses : List Bounds) : Op → Option (Bounds × List Bounds)
  | .literal n d => some (⟨n*s/(d : Int), ceilDiv (n*s) d⟩, witnesses)
  | .copy a => do return (← stack[a]?, witnesses)
  | .add a b => do
    let A ← stack[a]?
    let B ← stack[b]?
    return (⟨A.lo+B.lo, A.hi+B.hi⟩, witnesses)
  | .neg a => do
    let A ← stack[a]?
    return (⟨-A.hi,-A.lo⟩, witnesses)
  | .mul a b => do
    let A ← stack[a]?
    let B ← stack[b]?
    let lo := min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi))
    let hi := max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi))
    return (⟨lo/s, ceilDiv hi s⟩, witnesses)
  | .inv a => do
    let A ← stack[a]?
    return (⟨(s : Int)^2/A.hi, ceilDiv ((s : Int)^2) A.lo⟩, witnesses)
  | .cubic _ _ => match witnesses with
    | [] => none
    | W :: rest => some (W, rest)

/--
Defines `evalStep` of type `Option (Bounds × List Bounds)` by `do let (R, rest) ← proposeOp s
stack witnesses op if op.check s stack R then return (R, rest) else none`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalProgram_length` uses this definition to
establish exact identity `output.length = ops.length + stack.length`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def evalStep (s : Nat) (stack witnesses : List Bounds) (op : Op) :
    Option (Bounds × List Bounds) := do
  let (R, rest) ← proposeOp s stack witnesses op
  if op.check s stack R then return (R, rest) else none

/--
The precise assertion is `R.Mem s (op.value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalProgram_sound` uses this assertion to
establish the precise assertion is `Encloses s output (codeValue v ops)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Separate `op.check s stack p.1 = true` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem evalStep_sound {s : Nat} (hs : 0 < s) {stack witnesses : List Bounds}
    {op : Op} {R : Bounds} {rest : List Bounds} {v : Nat → ℝ}
    (hv : Encloses s stack v) (hc : evalStep s stack witnesses op = some (R, rest)) :
    R.Mem s (op.value v) := by
  -- Separate `op.check s stack p.1 = true` from its negation; prove the goal under each of
  -- these mutually exclusive hypotheses.
  cases hp : proposeOp s stack witnesses op with
  | none => simp [evalStep, hp] at hc
  | some p =>
    by_cases hh : op.check s stack p.1 = true
    · have he : p = (R, rest) := by simpa [evalStep, hp, hh] using hc
      subst p
      exact op.check_sound hs hv hh
    · simp [evalStep, hp, hh] at hc

/--
Defines `evalProgram` by pattern matching with result type `List Bounds → List Bounds → List Op
→ Option (List Bounds)`. The displayed branches determine the recursive cases and their
returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.evalCheck` uses this definition in the
displayed construction of `evalCheck`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Section 4.1.
-/
def evalProgram (s : Nat) : List Bounds → List Bounds → List Op → Option (List Bounds)
  | stack, witnesses, [] => if witnesses.isEmpty then some stack else none
  | stack, witnesses, op :: ops => do
    let (R, rest) ← evalStep s stack witnesses op
    evalProgram s (R :: stack) rest ops

/--
Defines `codeValue` by pattern matching with result type `(Nat → ℝ) → List Op → (Nat → ℝ)`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.codeExpression_value` rewrites with this
definition to establish the identity `(codeExpression E ops i).value v = codeValue (fun j =>
(E j).value v) ops i`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def codeValue : (Nat → ℝ) → List Op → (Nat → ℝ)
  | v, [] => v
  | v, op :: ops => codeValue (fun i => match i with
      | 0 => op.value v
      | j+1 => v j) ops

/--
The precise assertion is `Encloses s output (codeValue v ops)`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalSource_enclosed` uses this assertion to
establish the precise assertion is `I.Mem s (source.value v)`.

Article: chebyshev2, Section 4.1.

Proof: Induct on `ops` while keeping `stack witnesses v` arbitrary; the recursive step
uses the previous-stage assertion. Separate `witnesses.isEmpty = true` from its negation; prove
the goal under each of these mutually exclusive hypotheses.
-/
theorem evalProgram_sound {s : Nat} (hs : 0 < s) (ops : List Op)
    {stack witnesses output : List Bounds} {v : Nat → ℝ} (hv : Encloses s stack v)
    (hc : evalProgram s stack witnesses ops = some output) :
    Encloses s output (codeValue v ops) := by
  -- Induct on `ops` while keeping `stack witnesses v` arbitrary; the recursive step uses
  -- the previous-stage assertion.
  induction ops generalizing stack witnesses v with
  | nil =>
    by_cases hh : witnesses.isEmpty = true
    · have he : stack = output := by simpa [evalProgram, hh] using hc
      subst output
      exact hv
    · simp [evalProgram, hh] at hc
  | cons op ops ih =>
    cases hh : evalStep s stack witnesses op with
    | none => simp [evalProgram, hh] at hc
    | some p =>
      have hrest : evalProgram s (p.1 :: stack) p.2 ops = some output := by
        simpa [evalProgram, hh] using hc
      apply ih _ hrest
      intro i I hi
      cases i with
      | zero =>
        have he : p.1 = I := by simpa using hi
        subst I
        exact evalStep_sound hs hv hh
      | succ j => exact hv j I (by simpa using hi)

/--
Exact identity `(codeExpression E ops i).value v = codeValue (fun j => (E j).value v) ops i`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalSource_enclosed` rewrites with this
identity to establish `I.Mem s (source.value v)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `ops` while keeping `E` arbitrary; the recursive step uses the
previous-stage assertion. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem codeExpression_value (ops : List Op) (E : Nat → Expr) (v : Nat → ℝ)
    (i : Nat) : (codeExpression E ops i).value v =
      codeValue (fun j => (E j).value v) ops i := by
  -- Induct on `ops` while keeping `E` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction ops generalizing E with
  | nil => rfl
  | cons op ops ih =>
    rw [codeExpression, ih, codeValue]
    congr 1
    funext j
    cases j with
    | zero => exact op.expression_value E v
    | succ j => rfl

/--
The precise assertion is `I.Mem s (source.value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalRows_source_output` uses this assertion to
establish the precise assertion is `((evalOutput s [r.time, piBounds] r.roots ops)[i]!).Mem s
(source.value v)`.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.codeExpression_value`,
`chebyshev2.Numerics.IntegerCertificate.evalProgram_sound` with the arguments shown in the
proof.
-/
theorem evalSource_enclosed {s : Nat} (hs : 0 < s) (ops : List Op)
    {stack witnesses output : List Bounds} {v : Nat → ℝ} (hv : Encloses s stack v)
    (hc : evalProgram s stack witnesses ops = some output) {i : Nat} {source : Expr}
    (he : codeExpressionCheck ops i source = true) {I : Bounds}
    (hi : output[i]? = some I) : I.Mem s (source.value v) := by
  have hsource : codeExpression Expr.input ops i = source := of_decide_eq_true he
  rw [← hsource, codeExpression_value]
  exact evalProgram_sound hs ops hv hc i I hi

/--
Defines `evalCheck` of type `Bool` by `(evalProgram s stack witnesses ops).isSome`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalCheck_result` rewrites with this
definition to establish acceptance/decoding identity for the displayed finite data:
`evalProgram s stack witnesses ops = some (evalOutput s stack witnesses ops)`.

Article: chebyshev2, Section 4.1.
-/
def evalCheck (s : Nat) (stack witnesses : List Bounds) (ops : List Op) : Bool :=
  (evalProgram s stack witnesses ops).isSome

/--
Defines `evalOutput` of type `List Bounds` by `(evalProgram s stack witnesses ops).getD []`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalCheck_result` rewrites with this
definition to establish acceptance/decoding identity for the displayed finite data:
`evalProgram s stack witnesses ops = some (evalOutput s stack witnesses ops)`.

Article: chebyshev2, Section 4.1.
-/
def evalOutput (s : Nat) (stack witnesses : List Bounds) (ops : List Op) : List Bounds :=
  (evalProgram s stack witnesses ops).getD []

/--
Acceptance/decoding identity for the displayed finite data: `evalProgram s stack witnesses ops
= some (evalOutput s stack witnesses ops)`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalRows_source_output` uses this identity to
establish the precise assertion is `((evalOutput s [r.time, piBounds] r.roots ops)[i]!).Mem s
(source.value v)`.

Article: chebyshev2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem evalCheck_result {s : Nat} {stack witnesses : List Bounds} {ops : List Op}
    (hc : evalCheck s stack witnesses ops = true) :
    evalProgram s stack witnesses ops = some (evalOutput s stack witnesses ops) := by
  cases hh : evalProgram s stack witnesses ops with
  | none => simp [evalCheck, hh] at hc
  | some result => simp [evalOutput, hh]

/--
Exact identity `output.length = ops.length + stack.length`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalRows_source_output` rewrites with this
identity to establish `((evalOutput s [r.time, piBounds] r.roots
ops)[i]!).Mem s (source.value v)`.

Article: chebyshev2, Section 4.1.

Proof: Induct on `ops` while keeping `stack witnesses` arbitrary; the recursive step uses
the previous-stage assertion. Separate `witnesses.isEmpty = true` from its negation; prove the
goal under each of these mutually exclusive hypotheses.
-/
theorem evalProgram_length {s : Nat} (ops : List Op) {stack witnesses output : List Bounds}
    (hc : evalProgram s stack witnesses ops = some output) :
    output.length = ops.length + stack.length := by
  -- Induct on `ops` while keeping `stack witnesses` arbitrary; the recursive step uses
  -- the previous-stage assertion.
  induction ops generalizing stack witnesses with
  | nil =>
    by_cases hh : witnesses.isEmpty = true
    · have he : stack = output := by simpa [evalProgram, hh] using hc
      simp [← he]
    · simp [evalProgram, hh] at hc
  | cons op ops ih =>
    cases hh : evalStep s stack witnesses op with
    | none => simp [evalProgram, hh] at hc
    | some p =>
      have hrest : evalProgram s (p.1 :: stack) p.2 ops = some output := by
        simpa [evalProgram, hh] using hc
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ih hrest

/--
Input time and root intervals for scaled arithmetic evaluation. The soundness theorem
separately links these intervals to actual real inputs.

Use: `chebyshev2.Numerics.IntegerCertificate.evalRowsCheck` uses this record of data and
proof obligations in the displayed construction of `evalRowsCheck`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Section 4.1.
-/
structure EvalRow where
  /-- Scaled input time interval. -/
  time : Bounds
  /-- Proposed root/input enclosures supplied to the arithmetic evaluator. -/
  roots : List Bounds
  deriving Repr, DecidableEq

/--
Defines `evalRowsCheck` of type `Bool` by `rows.all (fun r => evalCheck s [r.time, piBounds]
r.roots ops)`.

Use: `chebyshev2.Numerics.IntegerCertificate.evalRows_source_output` uses this definition
to establish `((evalOutput s [r.time, piBounds] r.roots ops)[i]!).Mem
s (source.value v)`.

Article: chebyshev2, Section 4.1.
-/
def evalRowsCheck (s : Nat) (piBounds : Bounds) (ops : List Op) (rows : List EvalRow) : Bool :=
  rows.all (fun r => evalCheck s [r.time, piBounds] r.roots ops)

/--
The precise assertion is `((evalOutput s [r.time, piBounds] r.roots ops)[i]!).Mem s
(source.value v)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.evalCheck_result`,
`chebyshev2.Numerics.IntegerCertificate.evalProgram_length`,
`chebyshev2.Numerics.IntegerCertificate.evalSource_enclosed` with the arguments shown in
the proof.
-/
theorem evalRows_source_output {s : Nat} (hs : 0 < s) {piBounds : Bounds}
    {ops : List Op} {rows : List EvalRow} (hc : evalRowsCheck s piBounds ops rows = true)
    {r : EvalRow} (hr : r ∈ rows) {v : Nat → ℝ}
    (hv : Encloses s [r.time, piBounds] v) {i : Nat} (hindex : i < ops.length)
    {source : Expr} (he : codeExpressionCheck ops i source = true) :
    ((evalOutput s [r.time, piBounds] r.roots ops)[i]!).Mem s (source.value v) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.evalCheck_result`,
  -- `chebyshev2.Numerics.IntegerCertificate.evalProgram_length`,
  -- `chebyshev2.Numerics.IntegerCertificate.evalSource_enclosed` with the arguments shown
  -- in the proof.
  have hrow := List.all_eq_true.mp hc r hr
  have houtput := evalCheck_result hrow
  have hi : i < (evalOutput s [r.time, piBounds] r.roots ops).length := by
    rw [evalProgram_length ops houtput]
    simp only [List.length_cons, List.length_nil]
    omega
  apply evalSource_enclosed hs ops hv houtput he
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

end chebyshev2.Numerics.IntegerCertificate
