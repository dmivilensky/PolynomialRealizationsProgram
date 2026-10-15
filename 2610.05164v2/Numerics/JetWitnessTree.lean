import «2610.05164v2».Numerics.CachedJetExpr

/-!
Article: 2610.05164v2, Lemma 18.
`«2610.05164v2».Numerics.JetWitness.check_sound` checks each arithmetic node against checked
children, avoiding repeated nested jet expansion.
Interface: its result can discharge the corresponding enclosure premises of
`«2610.05164v2».Numerics.JetExpr.enclose_sound`.
Proof chain: 2610.05164v2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace «2610.05164v2».Numerics
open Set LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 2000000

deriving instance DecidableEq for JetExpr

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `«2610.05164v2».Numerics.JetWitness.check` uses this definition in the displayed
construction of `JetWitness.check`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
inductive JetWitness : JetExpr → Type where
  /-- Witness node for a rational constant jet. -/
  | literal (q : ℚ) : JetWitness (.literal q)
  /-- Witness node for the proved pi enclosure. -/
  | pi : JetWitness .pi
  /-- Witness node for the identity coordinate jet. -/
  | variable : JetWitness .variable
  /-- Child witnesses and interval jets for addition. -/
  | add {a b : JetExpr} (A B : IntervalJet) : JetWitness a → JetWitness b → JetWitness (.add a b)
  /-- Child witnesses and interval jets for multiplication. -/
  | mul {a b : JetExpr} (A B : IntervalJet) : JetWitness a → JetWitness b → JetWitness (.mul a b)
  /-- Child witness and jet for a square. -/
  | square {a : JetExpr} (A : IntervalJet) : JetWitness a → JetWitness (.square a)
  /-- Child witness and jet for negation. -/
  | neg {a : JetExpr} (A : IntervalJet) : JetWitness a → JetWitness (.neg a)
  /-- Child witness together with operand and proposed inverse jets; the checker verifies the inverse recurrence. -/
  | inverse {a : JetExpr} (A J : IntervalJet) : JetWitness a → JetWitness (.inverse a J)
  /-- Child witnesses together with coefficient and proposed root jets; the checker verifies the cubic recurrence. -/
  | cubic {a b : JetExpr} (A B J : IntervalJet) :
      JetWitness a → JetWitness b → JetWitness (.cubic a b J)
  /-- A supplied expression/jet enclosure node; the soundness theorem still requires the associated regularity/enclosure hypotheses. -/
  | enclosed (a : JetExpr) (J : IntervalJet) : JetWitness (.enclosed a J)

/--
Defines `JetWitness.cast` of type `JetWitness b` by `h ▸ w`.

Use: `«2610.05164v2».Numerics.JetWitness.check_cast` uses this definition to establish exact
identity `(w.cast h).check X N J=w.check X N J`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetWitness.cast {a b : JetExpr} (w : JetWitness a) (h : a=b) : JetWitness b := h ▸ w

/--
Defines `JetWitness.check` of type `Bool`. The displayed construction fixes its component data;
its proof fields enforce the listed compatibility properties.

Use: `«2610.05164v2».Numerics.JetWitness.add_checked` uses this definition to establish
acceptance/decoding identity for the displayed finite data: `(JetWitness.add A B wa wb).check X
N J=true`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetWitness.check {e : JetExpr} (w : JetWitness e) (X : IntervalRat) (N : ℕ)
    (J : IntervalJet) : Bool :=
  match w with
  | .literal q => (JetExpr.literal q).checkCachedInto X N J
  | .pi => JetExpr.pi.checkCachedInto X N J
  | .variable => JetExpr.variable.checkCachedInto X N J
  | .enclosed a K => (JetExpr.enclosed a K).checkCachedInto X N J
  | @JetWitness.add a b A B wa wb =>
      wa.check X N A && wb.check X N B &&
        (JetExpr.add (.enclosed a A) (.enclosed b B)).checkCachedInto X N J
  | @JetWitness.mul a b A B wa wb =>
      wa.check X N A && wb.check X N B &&
        (JetExpr.mul (.enclosed a A) (.enclosed b B)).checkCachedInto X N J
  | @JetWitness.square a A wa =>
      wa.check X N A && (JetExpr.square (.enclosed a A)).checkCachedInto X N J
  | @JetWitness.neg a A wa =>
      wa.check X N A && (JetExpr.neg (.enclosed a A)).checkCachedInto X N J
  | @JetWitness.inverse a A K wa =>
      wa.check X N A && (JetExpr.inverse (.enclosed a A) K).checkCachedInto X N J
  | @JetWitness.cubic a b A B K wa wb =>
      wa.check X N A && wb.check X N B &&
        (JetExpr.cubic (.enclosed a A) (.enclosed b B) K).checkCachedInto X N J

/--
Exact identity `(w.cast h).check X N J=w.check X N J`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem JetWitness.check_cast {a b : JetExpr} (w : JetWitness a) (h : a=b)
    (X : IntervalRat) (N : ℕ) (J : IntervalJet) :
    (w.cast h).check X N J=w.check X N J := by
  cases h
  rfl

/--
Acceptance/decoding identity for the displayed finite data: `(JetWitness.add A B wa wb).check X
N J=true`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem JetWitness.add_checked {a b : JetExpr} {A B J : IntervalJet}
    (wa : JetWitness a) (wb : JetWitness b)
    {X : IntervalRat} {N : ℕ} (ha : wa.check X N A=true) (hb : wb.check X N B=true)
    (hc : (JetExpr.add (.enclosed a A) (.enclosed b B)).checkCachedInto X N J=true) :
    (JetWitness.add A B wa wb).check X N J=true := by simpa only [check,ha,hb,Bool.true_and] using hc

/--
Acceptance/decoding identity for the displayed finite data: `(JetWitness.mul A B wa wb).check X
N J=true`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem JetWitness.mul_checked {a b : JetExpr} {A B J : IntervalJet}
    (wa : JetWitness a) (wb : JetWitness b)
    {X : IntervalRat} {N : ℕ} (ha : wa.check X N A=true) (hb : wb.check X N B=true)
    (hc : (JetExpr.mul (.enclosed a A) (.enclosed b B)).checkCachedInto X N J=true) :
    (JetWitness.mul A B wa wb).check X N J=true := by simpa only [check,ha,hb,Bool.true_and] using hc

/--
Acceptance/decoding identity for the displayed finite data: `(JetWitness.square A wa).check X N
J=true`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem JetWitness.square_checked {a : JetExpr} {A J : IntervalJet}
    (wa : JetWitness a)
    {X : IntervalRat} {N : ℕ} (ha : wa.check X N A=true)
    (hc : (JetExpr.square (.enclosed a A)).checkCachedInto X N J=true) :
    (JetWitness.square A wa).check X N J=true := by simpa only [check,ha,Bool.true_and] using hc

/--
Acceptance/decoding identity for the displayed finite data: `(JetWitness.neg A wa).check X N
J=true`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem JetWitness.neg_checked {a : JetExpr} {A J : IntervalJet}
    (wa : JetWitness a)
    {X : IntervalRat} {N : ℕ} (ha : wa.check X N A=true)
    (hc : (JetExpr.neg (.enclosed a A)).checkCachedInto X N J=true) :
    (JetWitness.neg A wa).check X N J=true := by simpa only [check,ha,Bool.true_and] using hc

/--
Acceptance/decoding identity for the displayed finite data: `(JetWitness.inverse A K wa).check
X N J=true`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem JetWitness.inverse_checked {a : JetExpr} {A K J : IntervalJet}
    (wa : JetWitness a)
    {X : IntervalRat} {N : ℕ} (ha : wa.check X N A=true)
    (hc : (JetExpr.inverse (.enclosed a A) K).checkCachedInto X N J=true) :
    (JetWitness.inverse A K wa).check X N J=true := by simpa only [check,ha,Bool.true_and] using hc

/--
Acceptance/decoding identity for the displayed finite data: `(JetWitness.cubic A B K wa
wb).check X N J=true`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem JetWitness.cubic_checked {a b : JetExpr} {A B K J : IntervalJet}
    (wa : JetWitness a) (wb : JetWitness b)
    {X : IntervalRat} {N : ℕ} (ha : wa.check X N A=true) (hb : wb.check X N B=true)
    (hc : (JetExpr.cubic (.enclosed a A) (.enclosed b B) K).checkCachedInto X N J=true) :
    (JetWitness.cubic A B K wa wb).check X N J=true := by simpa only [check,ha,hb,Bool.true_and] using hc

/--
The precise assertion is `JetEncloses J e.value s x N`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.profileTreeCheck_sound` uses this assertion to
establish the precise assertion is `(velocity R W).CachedValid s x N ∧ (amplitude R
W).CachedValid s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `w` while keeping `J` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem JetWitness.check_sound {e : JetExpr} (w : JetWitness e)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x∈s)
    {X : IntervalRat} (hX : x∈X) {N : ℕ} (hr : e.Regular s) (hv : e.CachedValid s x N)
    {J : IntervalJet} (hc : w.check X N J=true) : JetEncloses J e.value s x N := by
  -- Induct on `w` while keeping `J` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction w generalizing J with
  | literal q => exact JetExpr.checkCachedInto_sound hs hx hX hr hv hc
  | pi => exact JetExpr.checkCachedInto_sound hs hx hX hr hv hc
  | «variable» => exact JetExpr.checkCachedInto_sound hs hx hX hr hv hc
  | enclosed a K => exact JetExpr.checkCachedInto_sound hs hx hX hr hv hc
  | @add a b A B wa wb iha ihb =>
      simp only [check,Bool.and_eq_true] at hc
      have hA := iha hr.1 hv.1 hc.1.1
      have hB := ihb hr.2 hv.2 hc.1.2
      exact JetExpr.checkCachedInto_sound (e := .add (.enclosed a A) (.enclosed b B)) hs hx hX hr ⟨hA,hB⟩ hc.2
  | @mul a b A B wa wb iha ihb =>
      simp only [check,Bool.and_eq_true] at hc
      have hA := iha hr.1 hv.1 hc.1.1
      have hB := ihb hr.2 hv.2 hc.1.2
      exact JetExpr.checkCachedInto_sound (e := .mul (.enclosed a A) (.enclosed b B)) hs hx hX hr ⟨hA,hB⟩ hc.2
  | @square a A wa ih =>
      simp only [check,Bool.and_eq_true] at hc
      exact JetExpr.checkCachedInto_sound (e := .square (.enclosed a A)) hs hx hX hr (ih hr hv hc.1) hc.2
  | @neg a A wa ih =>
      simp only [check,Bool.and_eq_true] at hc
      exact JetExpr.checkCachedInto_sound (e := .neg (.enclosed a A)) hs hx hX hr (ih hr hv hc.1) hc.2
  | @inverse a A K wa ih =>
      simp only [check,Bool.and_eq_true] at hc
      exact JetExpr.checkCachedInto_sound (e := .inverse (.enclosed a A) K) hs hx hX hr (ih hr.1 hv hc.1) hc.2
  | @cubic a b A B K wa wb iha ihb =>
      simp only [check,Bool.and_eq_true] at hc
      have hA := iha hr.1.1 hv.1 hc.1.1
      have hB := ihb hr.1.2 hv.2 hc.1.2
      exact JetExpr.checkCachedInto_sound (e := .cubic (.enclosed a A) (.enclosed b B) K) hs hx hX hr ⟨hA,hB⟩ hc.2

end «2610.05164v2».Numerics
