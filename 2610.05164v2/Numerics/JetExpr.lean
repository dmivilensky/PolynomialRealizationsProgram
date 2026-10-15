import «2610.05164v2».Numerics.CubicJetCheck

/-!
Article: 2610.05164v2, Lemma 18.
`«2610.05164v2».Numerics.JetExpr.enclose_sound` evaluates proposed inverse/cubic jets only after
checking their defining recurrences.
Interface: its result can discharge the corresponding enclosure premises of
`«2610.05164v2».Numerics.flowCoefficientCheck_sound`.
Proof chain: 2610.05164v2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace «2610.05164v2».Numerics
open Set LeanCert.Core
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `«2610.05164v2».Numerics.JetExpr.Regular` uses this definition in the displayed
construction of `JetExpr.Regular`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
inductive JetExpr where
  /-- Constant rational function. -/
  | literal (q : ℚ)
  /-- Constant pi function. -/
  | pi
  /-- The identity coordinate function. -/
  | variable
  /-- Pointwise sum of expression functions. -/
  | add (a b : JetExpr)
  /-- Pointwise product of expression functions. -/
  | mul (a b : JetExpr)
  /-- Pointwise square, preserving repeated-variable dependence in the jet enclosure. -/
  | square (a : JetExpr)
  /-- Pointwise negation. -/
  | neg (a : JetExpr)
  /-- Pointwise reciprocal with a proposed interval jet; regularity excludes zeros. -/
  | inverse (a : JetExpr) (witness : IntervalJet)
  /-- The selected positive cubic root with a proposed root jet; sign and residual conditions are checked. -/
  | cubic (a b : JetExpr) (witness : IntervalJet)
  /-- The underlying expression with a proposed jet attached; attaching data leaves the real function unchanged. -/
  | enclosed (a : JetExpr) (witness : IntervalJet)

/--
Defines `JetExpr.value` by pattern matching with result type `JetExpr → ℝ → ℝ`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.JetExpr.Regular.mono` uses this definition to establish the
precise assertion is `e.Regular t`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
noncomputable def JetExpr.value : JetExpr → ℝ → ℝ
  | .literal q => fun _ => q
  | .pi => fun _ => Real.pi
  | .variable => fun t => t
  | .add a b => fun t => a.value t+b.value t
  | .mul a b => fun t => a.value t*b.value t
  | .square a => fun t => (a.value t)^2
  | .neg a => fun t => -a.value t
  | .inverse a _ => fun t => (a.value t)⁻¹
  | .cubic a b _ => fun t => positiveCubic (a.value t) (b.value t)
  | .enclosed a _ => a.value

/--
Defines `JetExpr.Regular` by pattern matching with result type `JetExpr → Prop`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.JetExpr.Regular.mono` uses this definition to establish the
precise assertion is `e.Regular t`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.Regular (s : Set ℝ) : JetExpr → Prop
  | .literal _ | .pi | .variable => True
  | .add a b | .mul a b => a.Regular s ∧ b.Regular s
  | .neg a | .square a => a.Regular s
  | .inverse a _ => a.Regular s ∧ ∀ t∈s,a.value t≠0
  | .cubic a b _ => (a.Regular s ∧ b.Regular s) ∧
      (∀ t∈s,0≤a.value t) ∧ ∀ t∈s,0<b.value t
  | .enclosed a _ => a.Regular s

/--
The precise assertion is `e.Regular t`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.graphCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses JC (C R W).value s x N ∧ JetEncloses JA (A R
W).value s x N ∧ JetEncloses JB (B R W sigma).value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `e`; the recursive step uses the previous-stage assertion.
-/
theorem JetExpr.Regular.mono {s t : Set ℝ} {e : JetExpr} (h : e.Regular s)
    (ht : t⊆s) : e.Regular t := by
  -- Induct on `e`; the recursive step uses the previous-stage assertion.
  induction e with
  | literal q => trivial
  | pi => trivial
  | «variable» => trivial
  | add a b iha ihb => exact ⟨iha h.1,ihb h.2⟩
  | mul a b iha ihb => exact ⟨iha h.1,ihb h.2⟩
  | neg a ih => exact ih h
  | square a ih => exact ih h
  | enclosed a J ih => exact ih h
  | inverse a J ih => exact ⟨ih h.1,fun x hx => h.2 x (ht hx)⟩
  | cubic a b J iha ihb =>
    exact ⟨⟨iha h.1.1,ihb h.1.2⟩,fun x hx => h.2.1 x (ht hx),fun x hx => h.2.2 x (ht hx)⟩

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ e.value s`.

Use: `«2610.05164v2».Numerics.JetExpr.enclose_sound` uses this assertion to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `e`; the recursive step uses the previous-stage assertion.
-/
theorem JetExpr.Regular.smooth {s : Set ℝ} {e : JetExpr} (h : e.Regular s) :
    ContDiffOn ℝ ∞ e.value s := by
  -- Induct on `e`; the recursive step uses the previous-stage assertion.
  induction e with
  | literal q => exact contDiffOn_const
  | pi => exact contDiffOn_const
  | «variable» => exact contDiffOn_id
  | add a b iha ihb => exact (iha h.1).add (ihb h.2)
  | mul a b iha ihb => exact (iha h.1).mul (ihb h.2)
  | neg a ih => exact (ih h).neg
  | square a ih => exact (ih h).pow 2
  | enclosed a J ih => exact ih h
  | inverse a J ih => exact (ih h.1).inv h.2
  | cubic a b J iha ihb => exact positiveCubic_smooth (iha h.1.1) (ihb h.1.2) h.2.1 h.2.2

/--
Defines `intervalConstantJet` of type `IntervalJet` by `tabulateJet N (fun j => if j=0 then I
else IntervalRat.singleton 0)`.

Use: `«2610.05164v2».Numerics.intervalConstantJet_encloses` rewrites with this definition to
establish the stated quantitative bound `JetEncloses (intervalConstantJet I N) (fun _ => c) s x
N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def intervalConstantJet (I : IntervalRat) (N : ℕ) : IntervalJet :=
  tabulateJet N (fun j => if j=0 then I else IntervalRat.singleton 0)

/--
The stated quantitative bound `JetEncloses (intervalConstantJet I N) (fun _ => c) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.enclose_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `j=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem intervalConstantJet_encloses {I : IntervalRat} {c : ℝ} (hc : c∈I)
    (N : ℕ) (s : Set ℝ) (x : ℝ) :
    JetEncloses (intervalConstantJet I N) (fun _ => c) s x N := by
  -- Separate `j=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  intro j hj
  rw [intervalConstantJet,jetAt_tabulateJet hj]
  by_cases h : j=0
  · subst j; simpa using hc
  · rw [ite_eq_right h,normalizedWithin_const (Nat.pos_of_ne_zero h)]
    simpa using IntervalRat.mem_singleton 0

/--
Defines `JetExpr.enclose` by pattern matching with result type `JetExpr → Option IntervalJet`.
The displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.JetExpr.enclose_sound` uses this definition to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.enclose (X : IntervalRat) (N : ℕ) : JetExpr → Option IntervalJet
  | .literal q => some (constantJet q N)
  | .pi => some (intervalConstantJet piHigh N)
  | .variable => some (variableJet X N)
  | .add a b => do return addJet (← a.enclose X N) (← b.enclose X N) N
  | .mul a b => do return mulJet (← a.enclose X N) (← b.enclose X N) N
  | .square a => do return squareJet (← a.enclose X N) N
  | .neg a => do return negJet (← a.enclose X N) N
  | .inverse a J => do
    let A ← a.enclose X N
    if reciprocalJetCheck A J N then return J else none
  | .cubic a b J => do
    let A ← a.enclose X N
    let B ← b.enclose X N
    if cubicJetCheck A B J N then return J else none
  | .enclosed a J => do
    let A ← a.enclose X N
    if jetSubsetCheck A J N then return J else none

/--
The precise assertion is `JetEncloses J e.value s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.checkInto_sound` uses this assertion to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `e` while keeping `J` arbitrary; the recursive step uses the
previous-stage assertion. Separate `jetSubsetCheck A W N=true` from its negation; prove the
goal under each of these mutually exclusive hypotheses.
-/
theorem JetExpr.enclose_sound {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {x : ℝ} (hx : x∈s) {X : IntervalRat} (hX : x∈X) (N : ℕ) (e : JetExpr)
    (hr : e.Regular s) {J : IntervalJet} (h : e.enclose X N=some J) :
    JetEncloses J e.value s x N := by
  -- Induct on `e` while keeping `J` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction e generalizing J with
  | literal q => cases h; exact constantJet_encloses q N s x
  | pi => cases h; exact intervalConstantJet_encloses mem_piHigh N s x
  | «variable» => cases h; exact variableJet_encloses hX N hs hx
  | add a b iha ihb =>
    cases ha : a.enclose X N with
    | none => simp [enclose,ha] at h
    | some A =>
      cases hb : b.enclose X N with
      | none => simp [enclose,ha,hb] at h
      | some B =>
        simp [enclose,ha,hb] at h
        subst J
        exact addJet_encloses hs hx (hr.1.smooth.of_le (by simp) x hx)
          (hr.2.smooth.of_le (by simp) x hx) (iha hr.1 ha) (ihb hr.2 hb)
  | mul a b iha ihb =>
    cases ha : a.enclose X N with
    | none => simp [enclose,ha] at h
    | some A =>
      cases hb : b.enclose X N with
      | none => simp [enclose,ha,hb] at h
      | some B =>
        simp [enclose,ha,hb] at h
        subst J
        exact mulJet_encloses hs hx (hr.1.smooth.of_le (by simp) x hx)
          (hr.2.smooth.of_le (by simp) x hx) (iha hr.1 ha) (ihb hr.2 hb)
  | square a ih =>
    cases ha : a.enclose X N with
    | none => simp [enclose,ha] at h
    | some A =>
      simp [enclose,ha] at h
      subst J
      have hrA : a.Regular s := hr
      exact squareJet_encloses (f := a.value) (N := N) hs hx
        (hrA.smooth.of_le (by simp) x hx) (ih hrA ha)
  | neg a ih =>
    cases ha : a.enclose X N with
    | none => simp [enclose,ha] at h
    | some A =>
      simp [enclose,ha] at h
      subst J
      exact negJet_encloses (ih hr ha)
  | enclosed a W ih =>
    cases ha : a.enclose X N with
    | none => simp [enclose,ha] at h
    | some A =>
      by_cases hc : jetSubsetCheck A W N=true
      · simp [enclose,ha,hc] at h
        subst J
        exact jetSubsetCheck_sound hc (ih hr ha)
      · simp [enclose,ha,hc] at h
  | inverse a W ih =>
    cases ha : a.enclose X N with
    | none => simp [enclose,ha] at h
    | some A =>
      by_cases hc : reciprocalJetCheck A W N=true
      · simp [enclose,ha,hc] at h
        subst J
        exact reciprocalJetCheck_encloses hc hs hx (hr.1.smooth.of_le (by simp) x hx)
          hr.2 (ih hr.1 ha)
      · simp [enclose,ha,hc] at h
  | cubic a b W iha ihb =>
    cases ha : a.enclose X N with
    | none => simp [enclose,ha] at h
    | some A =>
      cases hb : b.enclose X N with
      | none => simp [enclose,ha,hb] at h
      | some B =>
        by_cases hc : cubicJetCheck A B W N=true
        · simp [enclose,ha,hb,hc] at h
          subst J
          exact cubicJetCheck_encloses hc hs hx (hr.1.1.smooth.of_le (by simp))
            (hr.1.2.smooth.of_le (by simp)) hr.2.1 hr.2.2 (iha hr.1.1 ha) (ihb hr.1.2 hb)
        · simp [enclose,ha,hb,hc] at h

end «2610.05164v2».Numerics
