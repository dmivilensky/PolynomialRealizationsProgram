import chebyshev2.Numerics.ExpHigh

/-!
Article: chebyshev2, Lemma 21.
`chebyshev2.Numerics.FlowStep.Coefficients` separates actual ODE coefficients from proposed
polynomial and tube witnesses.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.FlowStep.check_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
set_option autoImplicit false

/--
Proposed local Taylor-flow data: center/width, initial uncertainty, coefficient jets, a state
tube, remainder budget and output interval. Separate checker hypotheses make the enclosure
sound for the actual ODE.

Use: `chebyshev2.Numerics.FlowStep.Coefficients` uses this record of data and proof
obligations in the displayed construction of `FlowStep.Coefficients`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
structure FlowStep where
  /-- Taylor order used by the flow-step enclosure. -/
  order : ℕ
  /-- Rational center of the local time expansion. -/
  center : ℚ
  /-- Rational width of the step. -/
  width : ℚ
  /-- Enclosure of the actual initial state. -/
  initial : IntervalRat
  /-- State tube on which the ODE remainder estimates are checked. -/
  tube : IntervalRat
  /-- Initial-value uncertainty included in the validated flow bound. -/
  initialRadius : ℚ
  /-- Proposed remainder bound, subsequently required by the flow-step checker. -/
  remainder : ℚ
  /-- Coefficient jet for C at the expansion center. -/
  pointC : IntervalJet
  /-- Coefficient jet for A at the expansion center. -/
  pointA : IntervalJet
  /-- Coefficient jet for B at the expansion center. -/
  pointB : IntervalJet
  /-- Coefficient jet bounding C throughout the time cell. -/
  wholeC : IntervalJet
  /-- Coefficient jet bounding A throughout the time cell. -/
  wholeA : IntervalJet
  /-- Coefficient jet bounding B throughout the time cell. -/
  wholeB : IntervalJet
  /-- Reference-solution jet at the expansion center. -/
  pointR : IntervalJet
  /-- Reference-solution jet throughout the time cell. -/
  wholeR : IntervalJet
  /-- Proposed final-state enclosure produced by the checked flow step. -/
  output : IntervalRat

/--
Defines `FlowStep.slope` of type `ℚ` by `(riccatiSlope (jetAt W.wholeA 0) (jetAt W.wholeB 0)
W.tube).hi`.

Use: `chebyshev2.Numerics.FlowStep.rangeError` uses this definition in the displayed
construction of `FlowStep.rangeError`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.slope (W : FlowStep) : ℚ :=
  (riccatiSlope (jetAt W.wholeA 0) (jetAt W.wholeB 0) W.tube).hi

/--
Defines `FlowStep.rangePolynomial` of type `IntervalRat` by `sumIntervals (fun j => roundHigh
(IntervalRat.mul (if j=0 then IntervalRat.singleton W.center else jetAt W.pointR j) (powerHigh
V j))) (W.order+1)`.

Use: `chebyshev2.Numerics.FlowStep.polynomial` uses this definition in the displayed
construction of `FlowStep.polynomial`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.rangePolynomial (W : FlowStep) (V : IntervalRat) : IntervalRat :=
  sumIntervals (fun j => roundHigh (IntervalRat.mul
    (if j=0 then IntervalRat.singleton W.center else jetAt W.pointR j)
    (powerHigh V j))) (W.order+1)

/--
Defines `FlowStep.rangeError` of type `IntervalRat` by `IntervalRat.add (IntervalRat.mul
(IntervalRat.singleton W.remainder) (powerHigh V (W.order+1))) (IntervalRat.mul
(IntervalRat.singleton W.initialRadius) (expHigh (IntervalRat.mul (IntervalRat.singleton
W.slope) V)))`.

Use: `chebyshev2.Numerics.FlowStep.error` uses this definition in the displayed
construction of `FlowStep.error`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.rangeError (W : FlowStep) (V : IntervalRat) : IntervalRat :=
  IntervalRat.add
    (IntervalRat.mul (IntervalRat.singleton W.remainder) (powerHigh V (W.order+1)))
    (IntervalRat.mul (IntervalRat.singleton W.initialRadius)
      (expHigh (IntervalRat.mul (IntervalRat.singleton W.slope) V)))

/--
Defines `FlowStep.rangeRadius` of type `ℚ` by `max 0 (W.rangeError V).hi`.

Use: `chebyshev2.Numerics.FlowStep.errorRadius` uses this definition in the displayed
construction of `FlowStep.errorRadius`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.rangeRadius (W : FlowStep) (V : IntervalRat) : ℚ := max 0 (W.rangeError V).hi

/--
Defines `FlowStep.rangeEnclosure` of type `IntervalRat` by `IntervalRat.add (W.rangePolynomial
V) ⟨-W.rangeRadius V,W.rangeRadius V,neg_le_self (le_max_left _ _)⟩`.

Use: `chebyshev2.Numerics.FlowStep.enclosure` uses this definition in the displayed
construction of `FlowStep.enclosure`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.rangeEnclosure (W : FlowStep) (V : IntervalRat) : IntervalRat :=
  IntervalRat.add (W.rangePolynomial V)
    ⟨-W.rangeRadius V,W.rangeRadius V,neg_le_self (le_max_left _ _)⟩

/--
Defines `FlowStep.polynomial` of type `IntervalRat` by `W.rangePolynomial
(IntervalRat.singleton W.width)`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.polynomial (W : FlowStep) : IntervalRat :=
  W.rangePolynomial (IntervalRat.singleton W.width)
/--
Defines `FlowStep.error` of type `IntervalRat` by `W.rangeError (IntervalRat.singleton
W.width)`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.error (W : FlowStep) : IntervalRat :=
  W.rangeError (IntervalRat.singleton W.width)
/--
Defines `FlowStep.errorRadius` of type `ℚ` by `W.rangeRadius (IntervalRat.singleton W.width)`.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.errorRadius (W : FlowStep) : ℚ :=
  W.rangeRadius (IntervalRat.singleton W.width)
/--
Defines `FlowStep.enclosure` of type `IntervalRat` by `W.rangeEnclosure (IntervalRat.singleton
W.width)`.

Use: `chebyshev2.Numerics.FlowStep.check` uses this definition in the displayed
construction of `FlowStep.check`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.enclosure (W : FlowStep) : IntervalRat :=
  W.rangeEnclosure (IntervalRat.singleton W.width)

/--
Defines `FlowStep.check` of type `Bool`. The displayed construction fixes its component data;
its proof fields enforce the listed compatibility properties.

Use: `chebyshev2.Numerics.FlowStep.check_range_sound` rewrites with this definition to
establish membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def FlowStep.check (W : FlowStep) : Bool :=
  decide (0<W.width ∧ 0≤W.initialRadius ∧ 0≤W.remainder ∧
    W.center-W.initialRadius≤W.initial.lo ∧ W.initial.hi≤W.center+W.initialRadius ∧
    -W.remainder≤(jetAt W.wholeR (W.order+1)).lo ∧
    (jetAt W.wholeR (W.order+1)).hi≤W.remainder) &&
  flowTubeCheck W.initial W.tube (jetAt W.wholeC 0) (jetAt W.wholeA 0)
    (jetAt W.wholeB 0) W.center W.width &&
  riccatiJetCheck W.pointC W.pointA W.pointB W.pointR
    (IntervalRat.singleton W.center) W.order &&
  riccatiJetCheck W.wholeC W.wholeA W.wholeB W.wholeR W.tube (W.order+1) &&
  intervalSubsetCheck W.enclosure W.output

/--
Defines `FlowStep.Coefficients` of type `Prop`. The displayed construction fixes its component
data; its proof fields enforce the listed compatibility properties.

Use: `chebyshev2.Numerics.FlowStep.check_range_sound` uses this definition to establish
membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
noncomputable def FlowStep.Coefficients (W : FlowStep) (C A B : ℝ → ℝ) (a : ℝ) : Prop :=
  ContDiffOn ℝ (W.order+1) C (Icc a (a+W.width)) ∧
  ContDiffOn ℝ (W.order+1) A (Icc a (a+W.width)) ∧
  ContDiffOn ℝ (W.order+1) B (Icc a (a+W.width)) ∧
  (∀ j<W.order,
    normalizedWithin C (Icc a (a+W.width)) j a∈jetAt W.pointC j ∧
    normalizedWithin A (Icc a (a+W.width)) j a∈jetAt W.pointA j ∧
    normalizedWithin B (Icc a (a+W.width)) j a∈jetAt W.pointB j) ∧
  ∀ t∈Icc a (a+W.width),∀ j<W.order+1,
    normalizedWithin C (Icc a (a+W.width)) j t∈jetAt W.wholeC j ∧
    normalizedWithin A (Icc a (a+W.width)) j t∈jetAt W.wholeA j ∧
    normalizedWithin B (Icc a (a+W.width)) j t∈jetAt W.wholeB j

end chebyshev2.Numerics
