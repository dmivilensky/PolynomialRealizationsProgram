import chebyshev2.Numerics.IntegerExpression

/-!
Article: chebyshev2, Appendix F.2.
`chebyshev2.Numerics.IntegerCertificate.rows_source_output` exposes source-function bounds on a
complete integer partition.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.actualJetCover_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics.IntegerCertificate
set_option autoImplicit false

/--
A scaled time cell carrying a list of state-coordinate enclosures. Its role in coverage is
determined by the explicit partition checker.

Use: `chebyshev2.Numerics.IntegerCertificate.rowCheck` uses this record of data and proof
obligations in the displayed construction of `rowCheck`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
structure Row where
  /-- Scaled time interval of the cell. -/
  time : Bounds
  /-- State-coordinate enclosures associated with that time interval. -/
  values : List Bounds
  deriving Repr, DecidableEq

/--
Defines `partitionCheck` by pattern matching with result type `List Bounds → Bool`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntegerCertificate.partitionCheck_cover` uses this definition to
establish constructs witnesses with the exact properties `∃ I ∈ cells, I.Mem s x`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def partitionCheck (left right : Int) : List Bounds → Bool
  | [] => decide (left = right)
  | I :: rest => decide (I.lo = left ∧ I.lo < I.hi) && partitionCheck I.hi right rest

/--
Constructs witnesses with the exact properties `∃ I ∈ cells, I.Mem s x`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.covers` uses this assertion to
establish constructs witnesses with the exact properties `∃ r∈rows, t∈Icc (r.left scale)
(r.right scale)`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `cells` while keeping `left` arbitrary; the recursive step uses the
previous-stage assertion. Separate `(s : ℝ)*x ≤ (I.hi : ℝ)` from its negation; prove the goal
under each of these mutually exclusive hypotheses.
-/
theorem partitionCheck_cover {s : Nat} {left right : Int} {cells : List Bounds}
    (hc : partitionCheck left right cells = true) (hn : cells ≠ [])
    {x : ℝ} (hl : (left : ℝ) ≤ (s : ℝ)*x) (hu : (s : ℝ)*x ≤ (right : ℝ)) :
    ∃ I ∈ cells, I.Mem s x := by
  -- Induct on `cells` while keeping `left` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction cells generalizing left with
  | nil => contradiction
  | cons I rest ih =>
    have hh : (I.lo = left ∧ I.lo < I.hi) ∧ partitionCheck I.hi right rest = true := by
      simpa only [partitionCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
    by_cases hx : (s : ℝ)*x ≤ (I.hi : ℝ)
    · exact ⟨I, by simp, by simpa [Bounds.Mem, hh.1.1] using And.intro hl hx⟩
    · have hrest : rest ≠ [] := by
        intro he
        rw [he] at hh
        have heq : I.hi = right := of_decide_eq_true hh.2
        exact hx (by simpa [heq] using hu)
      obtain ⟨J, hJ, hmem⟩ := ih hh.2 hrest (le_of_not_ge hx)
      exact ⟨J, by simp [hJ], hmem⟩

/--
Defines `rowCheck` of type `Bool` by `decide (r.values.length = ops.length) && programCheck s
[r.time, piBounds] (annotate ops r.values)`.

Use: `chebyshev2.Numerics.IntegerCertificate.rowsCheck` uses this definition in the
displayed construction of `rowsCheck`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def rowCheck (s : Nat) (piBounds : Bounds) (ops : List Op) (r : Row) : Bool :=
  decide (r.values.length = ops.length) &&
    programCheck s [r.time, piBounds] (annotate ops r.values)

/--
Defines `rowsCheck` of type `Bool` by `rows.all (rowCheck s piBounds ops)`.

Use: `chebyshev2.Numerics.IntegerCertificate.rowsCheck_row` uses this definition to
establish acceptance/decoding identity for the displayed finite data: `r.values.length =
ops.length ∧ programCheck s [r.time, piBounds] (annotate ops r.values) = true`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def rowsCheck (s : Nat) (piBounds : Bounds) (ops : List Op) (rows : List Row) : Bool :=
  rows.all (rowCheck s piBounds ops)

/--
Acceptance/decoding identity for the displayed finite data: `r.values.length = ops.length ∧
programCheck s [r.time, piBounds] (annotate ops r.values) = true`.

Use: `chebyshev2.Numerics.IntegerCertificate.rows_source_enclosed` uses this identity to
establish the precise assertion is `I.Mem s (source.value v)`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem rowsCheck_row {s : Nat} {piBounds : Bounds} {ops : List Op} {rows : List Row}
    (hc : rowsCheck s piBounds ops rows = true) {r : Row} (hr : r ∈ rows) :
    r.values.length = ops.length ∧
      programCheck s [r.time, piBounds] (annotate ops r.values) = true := by
  have hh := List.all_eq_true.mp hc r hr
  simpa only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] using hh

/--
The precise assertion is `I.Mem s (source.value v)`.

Use: `chebyshev2.Numerics.IntegerCertificate.rows_source_output` uses this assertion to
establish the precise assertion is `((programBounds [r.time, piBounds] (annotate ops
r.values))[i]!).Mem s (source.value v)`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.rowsCheck_row`,
`chebyshev2.Numerics.IntegerCertificate.source_enclosed`,
`chebyshev2.Numerics.IntegerCertificate.expressionCheck_of_code` with the arguments shown
in the proof.
-/
theorem rows_source_enclosed {s : Nat} (hs : 0 < s) {piBounds : Bounds}
    {ops : List Op} {rows : List Row} (hc : rowsCheck s piBounds ops rows = true)
    {r : Row} (hr : r ∈ rows) {v : Nat → ℝ}
    (hv : Encloses s [r.time, piBounds] v) {i : Nat} {source : Expr}
    (he : codeExpressionCheck ops i source = true) {I : Bounds}
    (hi : (programBounds [r.time, piBounds] (annotate ops r.values))[i]? = some I) :
    I.Mem s (source.value v) := by
  -- Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.rowsCheck_row`,
  -- `chebyshev2.Numerics.IntegerCertificate.source_enclosed`,
  -- `chebyshev2.Numerics.IntegerCertificate.expressionCheck_of_code` with the arguments
  -- shown in the proof.
  have hh := rowsCheck_row hc hr
  exact source_enclosed hs _ hv hh.2 (expressionCheck_of_code hh.1 he) hi

/--
Exact identity `(programBounds stack nodes).length = nodes.length + stack.length`.

Use: `chebyshev2.Numerics.IntegerCertificate.rows_source_output` rewrites with this
identity to establish `((programBounds [r.time, piBounds] (annotate
ops r.values))[i]!).Mem s (source.value v)`.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `nodes` while keeping `stack` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem programBounds_length (nodes : List Node) (stack : List Bounds) :
    (programBounds stack nodes).length = nodes.length + stack.length := by
  induction nodes generalizing stack with
  | nil => simp [programBounds]
  | cons node nodes ih =>
    simpa [programBounds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (node.result :: stack))

/--
The precise assertion is `((programBounds [r.time, piBounds] (annotate ops r.values))[i]!).Mem
s (source.value v)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.rowsCheck_row`,
`chebyshev2.Numerics.IntegerCertificate.programBounds_length`,
`chebyshev2.Numerics.IntegerCertificate.rows_source_enclosed` with the arguments shown in
the proof.
-/
theorem rows_source_output {s : Nat} (hs : 0 < s) {piBounds : Bounds}
    {ops : List Op} {rows : List Row} (hc : rowsCheck s piBounds ops rows = true)
    {r : Row} (hr : r ∈ rows) {v : Nat → ℝ}
    (hv : Encloses s [r.time, piBounds] v) {i : Nat} (hindex : i < ops.length)
    {source : Expr} (he : codeExpressionCheck ops i source = true) :
    ((programBounds [r.time, piBounds] (annotate ops r.values))[i]!).Mem s (source.value v) := by
  -- Use the identities/estimates `chebyshev2.Numerics.IntegerCertificate.rowsCheck_row`,
  -- `chebyshev2.Numerics.IntegerCertificate.programBounds_length`,
  -- `chebyshev2.Numerics.IntegerCertificate.rows_source_enclosed` with the arguments shown
  -- in the proof.
  have hl := (rowsCheck_row hc hr).1
  have hi : i < (programBounds [r.time, piBounds] (annotate ops r.values)).length := by
    simp only [programBounds_length, annotate, List.length_zipWith, hl, min_self,
      List.length_cons, List.length_nil]
    omega
  apply rows_source_enclosed hs hc hr hv he
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

end chebyshev2.Numerics.IntegerCertificate
