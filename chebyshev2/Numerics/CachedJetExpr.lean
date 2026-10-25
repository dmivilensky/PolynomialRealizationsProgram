import chebyshev2.Numerics.ReferenceJetSource

/-!
Article: chebyshev2, Lemma 18.
`chebyshev2.Numerics.JetExpr.encloseCached_sound` shares checked arithmetic subexpressions while
preserving their real-source derivative bounds.
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
Defines `scaleJet` of type `IntervalJet` by `tabulateJet N (fun j => roundHigh (IntervalRat.mul
(IntervalRat.singleton q) (jetAt J j)))`.

Use: `chebyshev2.Numerics.JetExpr.mulCached` uses this definition in the displayed
construction of `JetExpr.mulCached`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def scaleJet (q : ℚ) (J : IntervalJet) (N : ℕ) : IntervalJet :=
  tabulateJet N (fun j => roundHigh (IntervalRat.mul (IntervalRat.singleton q) (jetAt J j)))

/--
The stated quantitative bound `JetEncloses (scaleJet q J N) (fun t => (q:ℝ)*f t) s x N`.

Use: `chebyshev2.Numerics.JetExpr.mulCached_encloses` uses this identity to establish the
stated quantitative bound `JetEncloses (a.mulCached A B N) (fun t => a.value t*b.value t) s x
N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.jetAt_tabulateJet`,
`chebyshev2.Numerics.normalizedWithin_const_mul`, `chebyshev2.Numerics.mem_roundHigh`
with the arguments shown in the proof.
-/
theorem scaleJet_encloses {q : ℚ} {J : IntervalJet} {f : ℝ → ℝ}
    {s : Set ℝ} {x : ℝ} {N : ℕ} (hJ : JetEncloses J f s x N) :
    JetEncloses (scaleJet q J N) (fun t => (q:ℝ)*f t) s x N := by
  intro j hj
  rw [scaleJet,jetAt_tabulateJet hj,normalizedWithin_const_mul]
  exact mem_roundHigh (IntervalRat.mem_mul (IntervalRat.mem_singleton q) (hJ j hj))

/--
Defines `JetExpr.mulCached` of type `IntervalJet` by `match a with | .literal q => scaleJet q B
N | _ => mulJet A B N`.

Use: `chebyshev2.Numerics.JetExpr.encloseCached_sound` uses this definition to establish
the precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.mulCached (a : JetExpr) (A B : IntervalJet) (N : ℕ) : IntervalJet :=
  match a with
  | .literal q => scaleJet q B N
  | _ => mulJet A B N

/--
The stated quantitative bound `JetEncloses (a.mulCached A B N) (fun t => a.value t*b.value t) s
x N`.

Use: `chebyshev2.Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.scaleJet_encloses`,
`chebyshev2.Numerics.mulJet_encloses` with the arguments shown in the proof.
-/
theorem JetExpr.mulCached_encloses {a b : JetExpr} {A B : IntervalJet}
    {s : Set ℝ} {x : ℝ} {N : ℕ} (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (ha : ContDiffWithinAt ℝ N a.value s x) (hb : ContDiffWithinAt ℝ N b.value s x)
    (hA : JetEncloses A a.value s x N) (hB : JetEncloses B b.value s x N) :
    JetEncloses (a.mulCached A B N) (fun t => a.value t*b.value t) s x N := by
  cases a with
  | literal q => exact scaleJet_encloses hB
  | _ => exact mulJet_encloses hs hx ha hb hA hB

/--
Defines `JetExpr.squareCached` of type `IntervalJet` by `match a with | .literal q =>
constantJet (q^2) N | .pi => intervalConstantJet (squareHigh piHigh) N | _ => squareJet A N`.

Use: `chebyshev2.Numerics.JetExpr.encloseCached_sound` uses this definition to establish
the precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.squareCached (a : JetExpr) (A : IntervalJet) (N : ℕ) : IntervalJet :=
  match a with
  | .literal q => constantJet (q^2) N
  | .pi => intervalConstantJet (squareHigh piHigh) N
  | _ => squareJet A N

/--
The stated quantitative bound `JetEncloses (a.squareCached A N) (fun t => a.value t^2) s x N`.

Use: `chebyshev2.Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.constantJet_encloses`,
`chebyshev2.Numerics.intervalConstantJet_encloses`,
`chebyshev2.Numerics.mem_squareHigh` with the arguments shown in the proof.
-/
theorem JetExpr.squareCached_encloses {a : JetExpr} {A : IntervalJet}
    {s : Set ℝ} {x : ℝ} {N : ℕ} (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (ha : ContDiffWithinAt ℝ N a.value s x) (hA : JetEncloses A a.value s x N) :
    JetEncloses (a.squareCached A N) (fun t => a.value t^2) s x N := by
  -- Use the identities/estimates `chebyshev2.Numerics.constantJet_encloses`,
  -- `chebyshev2.Numerics.intervalConstantJet_encloses`,
  -- `chebyshev2.Numerics.mem_squareHigh` with the arguments shown in the proof.
  cases a with
  | literal q =>
    change JetEncloses (constantJet (q^2) N) (fun _ => (q:ℝ)^2) s x N
    convert constantJet_encloses (q^2) N s x using 1
    simp only [Rat.cast_pow]
  | pi => exact intervalConstantJet_encloses (mem_squareHigh mem_piHigh) N s x
  | _ => exact squareJet_encloses hs hx ha hA

/--
Defines `JetExpr.CachedValid` by pattern matching with result type `JetExpr → Prop`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.JetExpr.CachedValid.sum` uses this definition to establish the
precise assertion is `(JetExpr.sum es).CachedValid s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.CachedValid (s : Set ℝ) (x : ℝ) (N : ℕ) : JetExpr → Prop
  | .literal _ | .pi | .variable => True
  | .add a b | .mul a b | .cubic a b _ => a.CachedValid s x N ∧ b.CachedValid s x N
  | .neg a | .square a | .inverse a _ => a.CachedValid s x N
  | .enclosed a J => JetEncloses J a.value s x N

/--
Defines `JetExpr.encloseCached` by pattern matching with result type `JetExpr → Option
IntervalJet`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.JetExpr.checkCachedInto` uses this definition in the displayed
construction of `JetExpr.checkCachedInto`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.encloseCached (X : IntervalRat) (N : ℕ) : JetExpr → Option IntervalJet
  | .literal q => some (constantJet q N)
  | .pi => some (intervalConstantJet piHigh N)
  | .variable => some (variableJet X N)
  | .add a b => do return addJet (← a.encloseCached X N) (← b.encloseCached X N) N
  | .mul a b => do return a.mulCached (← a.encloseCached X N) (← b.encloseCached X N) N
  | .square a => do return a.squareCached (← a.encloseCached X N) N
  | .neg a => do return negJet (← a.encloseCached X N) N
  | .inverse a J => do
    let A ← a.encloseCached X N
    if reciprocalJetCheck A J N then return J else none
  | .cubic a b J => do
    let A ← a.encloseCached X N
    let B ← b.encloseCached X N
    if cubicJetCheck A B J N then return J else none
  | .enclosed _ J => some J

/--
The precise assertion is `JetEncloses J e.value s x N`.

Use: `chebyshev2.Numerics.JetExpr.checkCachedInto_sound` uses this assertion to establish
the precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `e` while keeping `J` arbitrary; the recursive step uses the
previous-stage assertion. Separate `reciprocalJetCheck A W N=true` from its negation; prove the
goal under each of these mutually exclusive hypotheses.
-/
theorem JetExpr.encloseCached_sound {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {x : ℝ} (hx : x∈s) {X : IntervalRat} (hX : x∈X) (N : ℕ) (e : JetExpr)
    (hr : e.Regular s) (hv : e.CachedValid s x N) {J : IntervalJet} (h : e.encloseCached X N=some J) :
    JetEncloses J e.value s x N := by
  -- Induct on `e` while keeping `J` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction e generalizing J with
  | literal q => cases h; exact constantJet_encloses q N s x
  | pi => cases h; exact intervalConstantJet_encloses mem_piHigh N s x
  | «variable» => cases h; exact variableJet_encloses hX N hs hx
  | add a b iha ihb =>
    cases ha : a.encloseCached X N with
    | none => simp [encloseCached,ha] at h
    | some A =>
      cases hb : b.encloseCached X N with
      | none => simp [encloseCached,ha,hb] at h
      | some B =>
        simp [encloseCached,ha,hb] at h
        subst J
        exact addJet_encloses hs hx (hr.1.smooth.of_le (by simp) x hx)
          (hr.2.smooth.of_le (by simp) x hx) (iha hr.1 hv.1 ha) (ihb hr.2 hv.2 hb)
  | mul a b iha ihb =>
    cases ha : a.encloseCached X N with
    | none => simp [encloseCached,ha] at h
    | some A =>
      cases hb : b.encloseCached X N with
      | none => simp [encloseCached,ha,hb] at h
      | some B =>
        simp [encloseCached,ha,hb] at h
        subst J
        exact mulCached_encloses hs hx (hr.1.smooth.of_le (by simp) x hx)
          (hr.2.smooth.of_le (by simp) x hx) (iha hr.1 hv.1 ha) (ihb hr.2 hv.2 hb)
  | square a ih =>
    cases ha : a.encloseCached X N with
    | none => simp [encloseCached,ha] at h
    | some A =>
      simp [encloseCached,ha] at h
      subst J
      have hrA : a.Regular s := hr
      exact squareCached_encloses (a := a) (N := N) hs hx
        (hrA.smooth.of_le (by simp) x hx) (ih hrA hv ha)
  | neg a ih =>
    cases ha : a.encloseCached X N with
    | none => simp [encloseCached,ha] at h
    | some A =>
      simp [encloseCached,ha] at h
      subst J
      exact negJet_encloses (ih hr hv ha)
  | enclosed a W _ =>
    cases h
    exact hv
  | inverse a W ih =>
    cases ha : a.encloseCached X N with
    | none => simp [encloseCached,ha] at h
    | some A =>
      by_cases hc : reciprocalJetCheck A W N=true
      · simp [encloseCached,ha,hc] at h
        subst J
        exact reciprocalJetCheck_encloses hc hs hx (hr.1.smooth.of_le (by simp) x hx)
          hr.2 (ih hr.1 hv ha)
      · simp [encloseCached,ha,hc] at h
  | cubic a b W iha ihb =>
    cases ha : a.encloseCached X N with
    | none => simp [encloseCached,ha] at h
    | some A =>
      cases hb : b.encloseCached X N with
      | none => simp [encloseCached,ha,hb] at h
      | some B =>
        by_cases hc : cubicJetCheck A B W N=true
        · simp [encloseCached,ha,hb,hc] at h
          subst J
          exact cubicJetCheck_encloses hc hs hx (hr.1.1.smooth.of_le (by simp))
            (hr.1.2.smooth.of_le (by simp)) hr.2.1 hr.2.2 (iha hr.1.1 hv.1 ha) (ihb hr.1.2 hv.2 hb)
        · simp [encloseCached,ha,hb,hc] at h


/--
Defines `JetExpr.checkCachedInto` of type `Bool` by `match e.encloseCached X N with | none =>
false | some K => jetSubsetCheck K J N`.

Use: `chebyshev2.Numerics.JetExpr.checkCachedInto_sound` uses this definition to establish
the precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.checkCachedInto (e : JetExpr) (X : IntervalRat) (N : ℕ) (J : IntervalJet) : Bool :=
  match e.encloseCached X N with
  | none => false
  | some K => jetSubsetCheck K J N

/--
The precise assertion is `JetEncloses J e.value s x N`.

Use: `chebyshev2.Numerics.JetWitness.check_sound` uses this assertion to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.jetSubsetCheck_sound`,
`chebyshev2.Numerics.JetExpr.encloseCached_sound` with the arguments shown in the proof.
-/
theorem JetExpr.checkCachedInto_sound {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {x : ℝ} (hx : x∈s) {X : IntervalRat} (hX : x∈X) {N : ℕ} {e : JetExpr}
    (hr : e.Regular s) (hv : e.CachedValid s x N) {J : IntervalJet}
    (h : e.checkCachedInto X N J=true) : JetEncloses J e.value s x N := by
  -- Use the identities/estimates `chebyshev2.Numerics.jetSubsetCheck_sound`,
  -- `chebyshev2.Numerics.JetExpr.encloseCached_sound` with the arguments shown in the
  -- proof.
  cases he : e.encloseCached X N with
  | none => simp [checkCachedInto,he] at h
  | some K =>
    exact jetSubsetCheck_sound (by simpa only [checkCachedInto,he] using h)
      (e.encloseCached_sound hs hx hX N hr hv he)

/--
Defines `JetExpr.body` by pattern matching with result type `JetExpr → JetExpr`. The displayed
branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.JetExpr.Regular.body` uses this definition to establish the
precise assertion is `e.body.Regular s`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetExpr.body : JetExpr → JetExpr
  | .enclosed a _ => a
  | a => a

/--
Exact identity `e.body.value=e.value`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem JetExpr.body_value (e : JetExpr) : e.body.value=e.value := by cases e <;> rfl

/--
The precise assertion is `e.body.Regular s`.

Use: `chebyshev2.Numerics.ReferenceJetSource.profileCheck_sound` uses this assertion to
establish the precise assertion is `(velocity R W).CachedValid s x N ∧ (amplitude R
W).CachedValid s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem JetExpr.Regular.body {s : Set ℝ} {e : JetExpr} (h : e.Regular s) : e.body.Regular s := by cases e <;> exact h

/--
The precise assertion is `(JetExpr.sum es).CachedValid s x N`.

Use: `chebyshev2.Numerics.ReferenceJetSource.profileCheck_sound` uses this assertion to
establish the precise assertion is `(velocity R W).CachedValid s x N ∧ (amplitude R
W).CachedValid s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `es`; the recursive step uses the previous-stage assertion.
-/
theorem JetExpr.CachedValid.sum {s : Set ℝ} {x : ℝ} {N : ℕ} {es : List JetExpr}
    (h : ∀ e∈es,e.CachedValid s x N) : (JetExpr.sum es).CachedValid s x N := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun a ha => h a (by simp [ha]))⟩

end chebyshev2.Numerics
