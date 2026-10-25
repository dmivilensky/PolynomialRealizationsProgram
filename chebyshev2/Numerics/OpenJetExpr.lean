import chebyshev2.Numerics.JetExpr

/-!
Article: chebyshev2, Lemma 18.
`chebyshev2.Numerics.OpenJetExpr.check_sound` checks arithmetic jets with analytic inputs and
derives bounds for their real semantics.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.flowCoefficientCheck_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `chebyshev2.Numerics.OpenJetExpr.Regular` uses this definition in the displayed
construction of `OpenJetExpr.Regular`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
inductive OpenJetExpr where
  /-- An actual input function selected from the external function environment. -/
  | input (i : ℕ)
  /-- Constant rational function. -/
  | literal (q : ℚ)
  /-- Constant pi function. -/
  | pi
  /-- The identity coordinate function. -/
  | variable
  /-- Pointwise sum with a proposed result jet. -/
  | add (a b : OpenJetExpr) (jet : IntervalJet)
  /-- Pointwise product with a proposed result jet. -/
  | mul (a b : OpenJetExpr) (jet : IntervalJet)
  /-- Pointwise square with a proposed result jet. -/
  | square (a : OpenJetExpr) (jet : IntervalJet)
  /-- Pointwise negation with a proposed result jet. -/
  | neg (a : OpenJetExpr) (jet : IntervalJet)
  /-- Pointwise reciprocal with a proposed jet; regularity and acceptance check nonvanishing. -/
  | inverse (a : OpenJetExpr) (jet : IntervalJet)
  /-- The selected positive cubic root with a proposed jet, subject to the cubic acceptance conditions. -/
  | cubic (a b : OpenJetExpr) (jet : IntervalJet)

/--
Defines `OpenJetExpr.value` by pattern matching with result type `OpenJetExpr → ℝ → ℝ`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.OpenJetExpr.Regular.smooth` uses this definition to establish
smoothness to the stated order: `ContDiffOn ℝ ∞ (e.value env) s`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
noncomputable def OpenJetExpr.value (env : ℕ → ℝ → ℝ) : OpenJetExpr → ℝ → ℝ
  | .input i => env i
  | .literal q => fun _ => q
  | .pi => fun _ => Real.pi
  | .variable => id
  | .add a b _ => fun t => a.value env t+b.value env t
  | .mul a b _ => fun t => a.value env t*b.value env t
  | .square a _ => fun t => (a.value env t)^2
  | .neg a _ => fun t => -a.value env t
  | .inverse a _ => fun t => (a.value env t)⁻¹
  | .cubic a b _ => fun t => positiveCubic (a.value env t) (b.value env t)

/--
Defines `OpenJetExpr.Regular` by pattern matching with result type `OpenJetExpr → Prop`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.OpenJetExpr.Regular.smooth` uses this definition to establish
smoothness to the stated order: `ContDiffOn ℝ ∞ (e.value env) s`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def OpenJetExpr.Regular (env : ℕ → ℝ → ℝ) (s : Set ℝ) : OpenJetExpr → Prop
  | .input i => ContDiffOn ℝ ∞ (env i) s
  | .literal _ | .pi | .variable => True
  | .add a b _ | .mul a b _ => a.Regular env s ∧ b.Regular env s
  | .square a _ | .neg a _ => a.Regular env s
  | .inverse a _ => a.Regular env s ∧ ∀ t∈s,a.value env t≠0
  | .cubic a b _ => (a.Regular env s ∧ b.Regular env s) ∧
      (∀ t∈s,0≤a.value env t) ∧ ∀ t∈s,0<b.value env t

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (e.value env) s`.

Use: `chebyshev2.Numerics.OpenJetExpr.check_sound` uses this assertion to establish the
precise assertion is `JetEncloses (e.output E X N) (e.value env) s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `e`; the recursive step uses the previous-stage assertion.
-/
theorem OpenJetExpr.Regular.smooth {env : ℕ → ℝ → ℝ} {s : Set ℝ} {e : OpenJetExpr}
    (h : e.Regular env s) : ContDiffOn ℝ ∞ (e.value env) s := by
  -- Induct on `e`; the recursive step uses the previous-stage assertion.
  induction e with
  | input i => exact h
  | literal q => exact contDiffOn_const
  | pi => exact contDiffOn_const
  | «variable» => exact contDiffOn_id
  | add a b J iha ihb => exact (iha h.1).add (ihb h.2)
  | mul a b J iha ihb => exact (iha h.1).mul (ihb h.2)
  | square a J ih => exact (ih h).pow 2
  | neg a J ih => exact (ih h).neg
  | inverse a J ih => exact (ih h.1).inv h.2
  | cubic a b J iha ihb => exact positiveCubic_smooth (iha h.1.1) (ihb h.1.2) h.2.1 h.2.2

/--
Defines `OpenJetExpr.output` by pattern matching with result type `OpenJetExpr → IntervalJet`.
The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.OpenJetExpr.check_sound` uses this definition to establish the
precise assertion is `JetEncloses (e.output E X N) (e.value env) s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def OpenJetExpr.output (E : ℕ → IntervalJet) (X : IntervalRat) (N : ℕ) : OpenJetExpr → IntervalJet
  | .input i => E i
  | .literal q => constantJet q N
  | .pi => intervalConstantJet piHigh N
  | .variable => variableJet X N
  | .add _ _ J | .mul _ _ J | .square _ J | .neg _ J | .inverse _ J | .cubic _ _ J => J

/--
Defines `OpenJetExpr.localCheck` by pattern matching with result type `OpenJetExpr → Bool`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.OpenJetExpr.check` uses this definition in the displayed
construction of `OpenJetExpr.check`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def OpenJetExpr.localCheck (E : ℕ → IntervalJet) (X : IntervalRat) (N : ℕ) : OpenJetExpr → Bool
  | .input _ | .literal _ | .pi | .variable => true
  | .add a b J => jetSubsetCheck (addJet (a.output E X N) (b.output E X N) N) J N
  | .mul a b J => jetSubsetCheck (mulJet (a.output E X N) (b.output E X N) N) J N
  | .square a J => jetSubsetCheck (squareJet (a.output E X N) N) J N
  | .neg a J => jetSubsetCheck (negJet (a.output E X N) N) J N
  | .inverse a J => reciprocalJetCheck (a.output E X N) J N
  | .cubic a b J => cubicJetCheck (a.output E X N) (b.output E X N) J N

/--
Defines `OpenJetExpr.check` by pattern matching with result type `OpenJetExpr → Bool`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.OpenJetExpr.check_sound` uses this definition to establish the
precise assertion is `JetEncloses (e.output E X N) (e.value env) s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def OpenJetExpr.check (E : ℕ → IntervalJet) (X : IntervalRat) (N : ℕ) : OpenJetExpr → Bool
  | .input _ | .literal _ | .pi | .variable => true
  | .add a b J => a.check E X N && b.check E X N && (add a b J).localCheck E X N
  | .mul a b J => a.check E X N && b.check E X N && (mul a b J).localCheck E X N
  | .square a J => a.check E X N && (square a J).localCheck E X N
  | .neg a J => a.check E X N && (neg a J).localCheck E X N
  | .inverse a J => a.check E X N && (inverse a J).localCheck E X N
  | .cubic a b J => a.check E X N && b.check E X N && (cubic a b J).localCheck E X N

/--
The precise assertion is `JetEncloses (e.output E X N) (e.value env) s x N`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.sourceCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses J (R.contactCoreIntegrand hσ) s x n`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `e`; the recursive step uses the previous-stage assertion.
-/
theorem OpenJetExpr.check_sound {env : ℕ → ℝ → ℝ} {E : ℕ → IntervalJet}
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x∈s)
    {X : IntervalRat} (hX : x∈X) {N : ℕ}
    (hE : ∀ i,JetEncloses (E i) (env i) s x N) (e : OpenJetExpr)
    (hr : e.Regular env s) (hc : e.check E X N=true) :
    JetEncloses (e.output E X N) (e.value env) s x N := by
  -- Induct on `e`; the recursive step uses the previous-stage assertion.
  induction e with
  | input i => exact hE i
  | literal q => exact constantJet_encloses q N s x
  | pi => exact intervalConstantJet_encloses mem_piHigh N s x
  | «variable» => exact variableJet_encloses hX N hs hx
  | add a b J iha ihb =>
    simp only [check,Bool.and_eq_true,localCheck] at hc
    exact jetSubsetCheck_sound hc.2 (addJet_encloses hs hx
      (hr.1.smooth.of_le (by simp) x hx) (hr.2.smooth.of_le (by simp) x hx)
      (iha hr.1 hc.1.1) (ihb hr.2 hc.1.2))
  | mul a b J iha ihb =>
    simp only [check,Bool.and_eq_true,localCheck] at hc
    exact jetSubsetCheck_sound hc.2 (mulJet_encloses hs hx
      (hr.1.smooth.of_le (by simp) x hx) (hr.2.smooth.of_le (by simp) x hx)
      (iha hr.1 hc.1.1) (ihb hr.2 hc.1.2))
  | square a J ih =>
    simp only [check,Bool.and_eq_true,localCheck] at hc
    have ha : a.Regular env s := hr
    exact jetSubsetCheck_sound hc.2 (squareJet_encloses hs hx
      (ha.smooth.of_le (by simp) x hx) (ih hr hc.1))
  | neg a J ih =>
    simp only [check,Bool.and_eq_true,localCheck] at hc
    exact jetSubsetCheck_sound hc.2 (negJet_encloses (ih hr hc.1))
  | inverse a J ih =>
    simp only [check,Bool.and_eq_true,localCheck] at hc
    exact reciprocalJetCheck_encloses hc.2 hs hx
      (hr.1.smooth.of_le (by simp) x hx) hr.2 (ih hr.1 hc.1)
  | cubic a b J iha ihb =>
    simp only [check,Bool.and_eq_true,localCheck] at hc
    exact cubicJetCheck_encloses hc.2 hs hx (hr.1.1.smooth.of_le (by simp))
      (hr.1.2.smooth.of_le (by simp)) hr.2.1 hr.2.2 (iha hr.1.1 hc.1.1) (ihb hr.1.2 hc.1.2)

end chebyshev2.Numerics
