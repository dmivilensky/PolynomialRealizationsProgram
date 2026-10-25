import chebyshev2.Numerics.HighPrecision

/-!
Article: chebyshev2, Section 4.1.
A rejecting, compositional checker for rational interval expressions.
Use: `chebyshev2.Numerics.IntervalExpr.enclose_sound` feeds
`chebyshev2.Certificates.Compact.ReferenceBase.reference_base_mem` (reference base mem).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
open LeanCert.Core
set_option autoImplicit false

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `chebyshev2.Numerics.IntervalExpr.enclose` uses this definition in the displayed
construction of `IntervalExpr.enclose`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
inductive IntervalExpr (d : ℕ) where
  /-- An exact rational constant. -/
  | literal (q : ℚ)
  /-- One of the finite real input coordinates. -/
  | variable (i : Fin d)
  /-- Addition of two real subexpressions. -/
  | add (a b : IntervalExpr d)
  /-- Negation of a real subexpression. -/
  | neg (a : IntervalExpr d)
  /-- Multiplication of two real subexpressions. -/
  | mul (a b : IntervalExpr d)
  /-- Reciprocal; the enclosure checker separately checks the denominator excludes zero. -/
  | inverse (a : IntervalExpr d)
  /-- A natural power of the subexpression. -/
  | power (a : IntervalExpr d) (n : ℕ)
  /-- Real exp, with the supplied series length controlling only the proposed enclosure algorithm. -/
  | exponential (a : IntervalExpr d) (terms : ℕ)
  /-- Real log, with the supplied series length controlling the enclosure; admissible input signs are checked separately. -/
  | logarithm (a : IntervalExpr d) (terms : ℕ)
  /-- The nonnegative real square root, with domain checks supplied by the enclosure algorithm. -/
  | squareRoot (a : IntervalExpr d)
  /-- The same real expression with an outward-rounded proposed interval; rounding leaves its real value unchanged. -/
  | rounded (a : IntervalExpr d)
  deriving Repr

/--
Defines `IntervalExpr.value` by pattern matching with result type `IntervalExpr d → ℝ`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntervalExpr.enclose_sound` uses this definition to establish
membership in the specified domain/enclosure: `e.value x∈I`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def IntervalExpr.value {d : ℕ} (x : Fin d → ℝ) : IntervalExpr d → ℝ
  | .literal q => q
  | .variable i => x i
  | .add a b => a.value x+b.value x
  | .neg a => -a.value x
  | .mul a b => a.value x*b.value x
  | .inverse a => (a.value x)⁻¹
  | .power a n => (a.value x)^n
  | .exponential a _ => Real.exp (a.value x)
  | .logarithm a _ => Real.log (a.value x)
  | .squareRoot a => Real.sqrt (a.value x)
  | .rounded a => a.value x

 /--
Defines `IntervalExpr.enclose` by pattern matching with result type `IntervalExpr d → Option
IntervalRat`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.IntervalExpr.enclose_sound` uses this definition to establish
membership in the specified domain/enclosure: `e.value x∈I`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def IntervalExpr.enclose {d : ℕ} (box : Fin d → IntervalRat) : IntervalExpr d → Option IntervalRat
  | .literal q => some (IntervalRat.singleton q)
  | .variable i => some (box i)
  | .add a b => do return IntervalRat.add (← a.enclose box) (← b.enclose box)
  | .neg a => do return IntervalRat.neg (← a.enclose box)
  | .mul a b => do return IntervalRat.mul (← a.enclose box) (← b.enclose box)
  | .inverse a => do
    let I ← a.enclose box
    if h : ¬I.containsZero then return IntervalRat.invNonzero ⟨I,h⟩ else none
  | .power a n => do return powerHigh (← a.enclose box) n
  | .exponential a n => do return IntervalRat.expComputable (← a.enclose box) n
  | .logarithm a n => do
    let I ← a.enclose box
    if 0<I.lo then return IntervalRat.logComputable I n else none
  | .squareRoot a => do return IntervalRat.sqrtIntervalTightPrec (← a.enclose box)
  | .rounded a => do return roundHigh (← a.enclose box)

 /--
Membership in the specified domain/enclosure: `e.value x∈I`.

Use: `chebyshev2.Numerics.IntervalExpr.strictNegative_sound` uses this assertion to
establish the stated quantitative bound `e.value x<0`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Induct on `e` while keeping `I` arbitrary; the recursive step uses the
previous-stage assertion. Separate `¬A.containsZero` from its negation; prove the goal under
each of these mutually exclusive hypotheses.
-/
theorem IntervalExpr.enclose_sound {d : ℕ} (e : IntervalExpr d) (box : Fin d → IntervalRat)
    {I : IntervalRat} (h : e.enclose box=some I) {x : Fin d → ℝ}
    (hx : ∀ i,x i∈box i) : e.value x∈I := by
  -- Induct on `e` while keeping `I` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction e generalizing I with
  | literal q => cases h;exact IntervalRat.mem_singleton q
  | «variable» i => cases h;exact hx i
  | add a b iha ihb =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      cases hb : b.enclose box with
      | none => simp [enclose,ha,hb] at h
      | some B =>
        simp [enclose,ha,hb] at h
        subst I
        exact IntervalRat.mem_add (iha ha) (ihb hb)
  | mul a b iha ihb =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      cases hb : b.enclose box with
      | none => simp [enclose,ha,hb] at h
      | some B =>
        simp [enclose,ha,hb] at h
        subst I
        exact IntervalRat.mem_mul (iha ha) (ihb hb)
  | neg a ih =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      simp [enclose,ha] at h
      subst I
      exact IntervalRat.mem_neg (ih ha)
  | inverse a ih =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      by_cases hn : ¬A.containsZero
      · simp [enclose,ha,hn] at h
        subst I
        have hv := ih ha
        apply IntervalRat.mem_invNonzero hv
        intro hz
        apply hn
        have hh : (A.lo:ℝ)≤0 ∧ 0≤(A.hi:ℝ) := by simpa [hz] using hv
        exact ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2⟩
      · simp [enclose,ha,hn] at h
  | power a n ih =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      simp [enclose,ha] at h
      subst I
      exact mem_powerHigh (ih ha) n
  | exponential a n ih =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      simp [enclose,ha] at h
      subst I
      exact IntervalRat.mem_expComputable (ih ha) n
  | logarithm a n ih =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      by_cases hp : 0<A.lo
      · simp [enclose,ha,hp] at h
        subst I
        exact IntervalRat.mem_logComputable (ih ha) hp n
      · simp [enclose,ha,hp] at h
  | squareRoot a ih =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      simp [enclose,ha] at h
      subst I
      exact IntervalRat.mem_sqrtIntervalTightPrec' (ih ha)
  | rounded a ih =>
    cases ha : a.enclose box with
    | none => simp [enclose,ha] at h
    | some A =>
      simp [enclose,ha] at h
      subst I
      exact mem_roundHigh (ih ha)

 /--
Defines `IntervalExpr.strictNegative` of type `Bool` by `match e.enclose box with | none =>
false | some I => decide (I.hi<0)`.

Use: `chebyshev2.Numerics.IntervalExpr.strictNegative_sound` uses this definition to
establish the stated quantitative bound `e.value x<0`.

Article: chebyshev2, Section 4.1.
-/
def IntervalExpr.strictNegative {d : ℕ} (e : IntervalExpr d) (box : Fin d → IntervalRat) : Bool :=
  match e.enclose box with
  | none => false
  | some I => decide (I.hi<0)

 /--
The stated quantitative bound `e.value x<0`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates `chebyshev2.Numerics.IntervalExpr.enclose_sound` with
the arguments shown in the proof.
-/
theorem IntervalExpr.strictNegative_sound {d : ℕ} (e : IntervalExpr d) (box : Fin d → IntervalRat)
    (h : e.strictNegative box=true) {x : Fin d → ℝ} (hx : ∀ i,x i∈box i) : e.value x<0 := by
  cases he : e.enclose box with
  | none => simp [strictNegative,he] at h
  | some I =>
    have hI : I.hi<0 := of_decide_eq_true (by simpa [strictNegative,he] using h)
    have hi : (I.hi:ℝ)<0 := by exact_mod_cast hI
    exact (e.enclose_sound box he hx).2.trans_lt hi

end chebyshev2.Numerics
