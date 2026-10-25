import chebyshev2.Numerics.StateJet
import chebyshev2.Numerics.HighPrecision

/-!
Article: chebyshev2, Lemma 24.
`chebyshev2.Numerics.StateIntervalJet.encloses_inverse` propagates rational enclosures of actual
values, gradients and Hessians for state-box bounds.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.StateJetOn.state_taylor_upper`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open LeanCert.Core Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Interval enclosures of a scalar state function, its gradient and its Hessian. The enclosure
predicate connects these candidate intervals to the actual StateJet.

Use: `chebyshev2.Numerics.StateIntervalJet.Encloses` uses this record of data and proof
obligations in the displayed construction of `Encloses`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
structure StateIntervalJet (d : ℕ) where
  /-- Enclosure of the scalar state function. -/
  value : IntervalRat
  /-- Enclosure of each coordinate gradient component. -/
  gradient : Fin d → IntervalRat
  /-- Enclosure of each coordinate Hessian entry. -/
  hessian : Fin d → Fin d → IntervalRat

namespace StateIntervalJet
variable {d : ℕ}

/--
Constructs `add` of type `StateIntervalJet d` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_add` uses this definition to establish
the precise assertion is `(J.add K).Encloses (F.add G)`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def add (F G : StateIntervalJet d) : StateIntervalJet d where
  value := IntervalRat.add F.value G.value
  gradient i := IntervalRat.add (F.gradient i) (G.gradient i)
  hessian i j := IntervalRat.add (F.hessian i j) (G.hessian i j)

/--
Constructs `mul` of type `StateIntervalJet d` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_mul` uses this definition to establish
the precise assertion is `(J.mul K).Encloses (F.mul G)`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def mul (F G : StateIntervalJet d) : StateIntervalJet d where
  value := roundHigh (IntervalRat.mul F.value G.value)
  gradient i := roundHigh (IntervalRat.add
    (IntervalRat.mul (F.gradient i) G.value) (IntervalRat.mul F.value (G.gradient i)))
  hessian i j := roundHigh (IntervalRat.add (IntervalRat.add (IntervalRat.add
    (IntervalRat.mul (F.hessian i j) G.value) (IntervalRat.mul (F.gradient i) (G.gradient j)))
    (IntervalRat.mul (F.gradient j) (G.gradient i))) (IntervalRat.mul F.value (G.hessian i j)))

/--
Constructs `compose` of type `StateIntervalJet d` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Numerics.StateIntervalJet.inverse` uses this definition in the displayed
construction of `inverse`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def compose (F : StateIntervalJet d) (φ φ₁ φ₂ : IntervalRat) : StateIntervalJet d where
  value := φ
  gradient i := roundHigh (IntervalRat.mul φ₁ (F.gradient i))
  hessian i j := roundHigh (IntervalRat.add
    (IntervalRat.mul (IntervalRat.mul φ₂ (F.gradient i)) (F.gradient j))
    (IntervalRat.mul φ₁ (F.hessian i j)))

/--
Defines `positivePart` of type `IntervalRat` by `⟨max I.lo 0,max I.hi 0,max_le_max I.le
le_rfl⟩`.

Use: `chebyshev2.Numerics.StateIntervalJet.mem_positivePart` uses this definition to
establish membership in the specified domain/enclosure: `max x 0∈positivePart I`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def positivePart (I : IntervalRat) : IntervalRat :=
  ⟨max I.lo 0,max I.hi 0,max_le_max I.le le_rfl⟩

/--
Membership in the specified domain/enclosure: `max x 0∈positivePart I`.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_psi` uses this assertion to establish
the precise assertion is `J.psi.Encloses F.psi`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mem_positivePart {I : IntervalRat} {x : ℝ} (hx : x∈I) : max x 0∈positivePart I := by
  simpa only [IntervalRat.mem_def,positivePart,Rat.cast_max,Rat.cast_zero] using
    And.intro (max_le_max hx.1 le_rfl) (max_le_max hx.2 le_rfl)

/--
Defines `psiArgument` of type `IntervalRat` by `positivePart (IntervalRat.add I
(IntervalRat.singleton (3/2)))`.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_psi` uses this definition to establish
the precise assertion is `J.psi.Encloses F.psi`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def psiArgument (I : IntervalRat) : IntervalRat :=
  positivePart (IntervalRat.add I (IntervalRat.singleton (3/2)))

/--
Defines `psiValue` of type `IntervalRat` by `roundHigh (IntervalRat.add (IntervalRat.add
(IntervalRat.neg I) (IntervalRat.singleton (-1/2))) (IntervalRat.mul (IntervalRat.singleton
(4/27)) (powerHigh (psiArgument I) 3)))`.

Use: `chebyshev2.Numerics.StateIntervalJet.psi` uses this definition in the displayed
construction of `psi`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def psiValue (I : IntervalRat) : IntervalRat :=
  roundHigh (IntervalRat.add (IntervalRat.add (IntervalRat.neg I) (IntervalRat.singleton (-1/2)))
    (IntervalRat.mul (IntervalRat.singleton (4/27)) (powerHigh (psiArgument I) 3)))

/--
Defines `psiFirst` of type `IntervalRat` by `roundHigh (IntervalRat.add (IntervalRat.singleton
(-1)) (IntervalRat.mul (IntervalRat.singleton (4/9)) (powerHigh (psiArgument I) 2)))`.

Use: `chebyshev2.Numerics.StateIntervalJet.psi` uses this definition in the displayed
construction of `psi`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def psiFirst (I : IntervalRat) : IntervalRat :=
  roundHigh (IntervalRat.add (IntervalRat.singleton (-1))
    (IntervalRat.mul (IntervalRat.singleton (4/9)) (powerHigh (psiArgument I) 2)))

/--
Defines `psiSecond` of type `IntervalRat` by `roundHigh (IntervalRat.mul (IntervalRat.singleton
(8/9)) (psiArgument I))`.

Use: `chebyshev2.Numerics.StateIntervalJet.psi` uses this definition in the displayed
construction of `psi`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def psiSecond (I : IntervalRat) : IntervalRat :=
  roundHigh (IntervalRat.mul (IntervalRat.singleton (8/9)) (psiArgument I))

/--
Defines `psi` of type `StateIntervalJet d` by `F.compose (psiValue F.value) (psiFirst F.value)
(psiSecond F.value)`.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_psi` uses this definition to establish
the precise assertion is `J.psi.Encloses F.psi`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def psi (F : StateIntervalJet d) : StateIntervalJet d :=
  F.compose (psiValue F.value) (psiFirst F.value) (psiSecond F.value)

/--
Defines `inverse` of type `Option (StateIntervalJet d)` by `if h : ¬F.value.containsZero then
let I := IntervalRat.invNonzero ⟨F.value,h⟩ some (F.compose I (IntervalRat.neg (powerHigh I 2))
(IntervalRat.mul (IntervalRat.singleton 2) (powerHigh I 3))) else none`.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_inverse` rewrites with this definition
to establish `K.Encloses (F.inverse hn)`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def inverse (F : StateIntervalJet d) : Option (StateIntervalJet d) :=
  if h : ¬F.value.containsZero then
    let I := IntervalRat.invNonzero ⟨F.value,h⟩
    some (F.compose I (IntervalRat.neg (powerHigh I 2))
      (IntervalRat.mul (IntervalRat.singleton 2) (powerHigh I 3)))
  else none

noncomputable section

/--
Defines `Encloses` of type `Prop` by `∀ x∈s,F.value x∈J.value ∧ (∀ i,F.gradient x i∈J.gradient
i) ∧ ∀ i j,F.hessian x i j∈J.hessian i j`.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_add` uses this definition to establish
the precise assertion is `(J.add K).Encloses (F.add G)`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def Encloses {s : Set (Fin d → ℝ)} (J : StateIntervalJet d) (F : StateJetOn s) : Prop :=
  ∀ x∈s,F.value x∈J.value ∧ (∀ i,F.gradient x i∈J.gradient i) ∧
    ∀ i j,F.hessian x i j∈J.hessian i j

/--
The precise assertion is `(J.add K).Encloses (F.add G)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem encloses_add {s : Set (Fin d → ℝ)} {J K : StateIntervalJet d} {F G : StateJetOn s}
    (hF : J.Encloses F) (hG : K.Encloses G) : (J.add K).Encloses (F.add G) := by
  intro x hx
  obtain ⟨hfv,hfg,hfh⟩ := hF x hx
  obtain ⟨hgv,hgg,hgh⟩ := hG x hx
  exact ⟨IntervalRat.mem_add hfv hgv,fun i => IntervalRat.mem_add (hfg i) (hgg i),
    fun i j => IntervalRat.mem_add (hfh i j) (hgh i j)⟩

/--
The precise assertion is `(J.mul K).Encloses (F.mul G)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_roundHigh` with the arguments
shown in the proof.
-/
theorem encloses_mul {s : Set (Fin d → ℝ)} {J K : StateIntervalJet d} {F G : StateJetOn s}
    (hF : J.Encloses F) (hG : K.Encloses G) : (J.mul K).Encloses (F.mul G) := by
  -- Use the identities/estimates `chebyshev2.Numerics.mem_roundHigh` with the arguments
  -- shown in the proof.
  intro x hx
  obtain ⟨hfv,hfg,hfh⟩ := hF x hx
  obtain ⟨hgv,hgg,hgh⟩ := hG x hx
  exact ⟨mem_roundHigh (IntervalRat.mem_mul hfv hgv),fun i => mem_roundHigh (IntervalRat.mem_add
    (IntervalRat.mem_mul (hfg i) hgv) (IntervalRat.mem_mul hfv (hgg i))),
    fun i j => mem_roundHigh (IntervalRat.mem_add (IntervalRat.mem_add (IntervalRat.mem_add
      (IntervalRat.mem_mul (hfh i j) hgv) (IntervalRat.mem_mul (hfg i) (hgg j)))
      (IntervalRat.mem_mul (hfg j) (hgg i))) (IntervalRat.mem_mul hfv (hgh i j)))⟩

/--
The precise assertion is `(J.compose I I₁ I₂).Encloses (F.compose φ φ₁ φ₂ hφ hφ₁)`.

Use: `chebyshev2.Numerics.StateIntervalJet.encloses_inverse` uses this assertion to
establish the precise assertion is `K.Encloses (F.inverse hn)`.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_roundHigh` with the arguments
shown in the proof.
-/
theorem encloses_compose {s : Set (Fin d → ℝ)} {J : StateIntervalJet d} {F : StateJetOn s}
    (hF : J.Encloses F) {φ φ₁ φ₂ : ℝ → ℝ} {I I₁ I₂ : IntervalRat}
    (hφ : ∀ x∈s,HasDerivAt φ (φ₁ (F.value x)) (F.value x))
    (hφ₁ : ∀ x∈s,HasDerivAt φ₁ (φ₂ (F.value x)) (F.value x))
    (hI : ∀ x∈s,φ (F.value x)∈I ∧ φ₁ (F.value x)∈I₁ ∧ φ₂ (F.value x)∈I₂) :
    (J.compose I I₁ I₂).Encloses (F.compose φ φ₁ φ₂ hφ hφ₁) := by
  -- Use the identities/estimates `chebyshev2.Numerics.mem_roundHigh` with the arguments
  -- shown in the proof.
  intro x hx
  obtain ⟨_,hfg,hfh⟩ := hF x hx
  obtain ⟨hi,hi₁,hi₂⟩ := hI x hx
  exact ⟨hi,fun i => mem_roundHigh (IntervalRat.mem_mul hi₁ (hfg i)),
    fun i j => mem_roundHigh (IntervalRat.mem_add
      (IntervalRat.mem_mul (IntervalRat.mem_mul hi₂ (hfg i)) (hfg j))
      (IntervalRat.mem_mul hi₁ (hfh i j)))⟩

/--
The precise assertion is `J.psi.Encloses F.psi`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates
`chebyshev2.Numerics.StateIntervalJet.encloses_compose`,
`chebyshev2.Numerics.StateIntervalJet.mem_positivePart`,
`chebyshev2.Numerics.mem_roundHigh` with the arguments shown in the proof.
-/
theorem encloses_psi {s : Set (Fin d → ℝ)} {J : StateIntervalJet d} {F : StateJetOn s}
    (hF : J.Encloses F) : J.psi.Encloses F.psi := by
  -- Use the identities/estimates `chebyshev2.Numerics.StateIntervalJet.encloses_compose`,
  -- `chebyshev2.Numerics.StateIntervalJet.mem_positivePart`,
  -- `chebyshev2.Numerics.mem_roundHigh` with the arguments shown in the proof.
  apply encloses_compose hF
  intro x hx
  have hf := (hF x hx).1
  have hp : max (F.value x+3/2) 0∈psiArgument J.value := by
    apply mem_positivePart
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      IntervalRat.mem_add hf (IntervalRat.mem_singleton (3/2))
  constructor
  · apply mem_roundHigh
    simpa only [chebyshev2.Residual.psi,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,
      sub_eq_add_neg,neg_div] using
      IntervalRat.mem_add (IntervalRat.mem_add (IntervalRat.mem_neg hf) (IntervalRat.mem_singleton (-1/2)))
        (IntervalRat.mem_mul (IntervalRat.mem_singleton (4/27)) (mem_powerHigh hp 3))
  constructor
  · apply mem_roundHigh
    simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
      IntervalRat.mem_add (IntervalRat.mem_singleton (-1))
        (IntervalRat.mem_mul (IntervalRat.mem_singleton (4/9)) (mem_powerHigh hp 2))
  · apply mem_roundHigh
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      IntervalRat.mem_mul (IntervalRat.mem_singleton (8/9)) hp

/--
The precise assertion is `K.Encloses (F.inverse hn)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `¬J.value.containsZero` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem encloses_inverse {s : Set (Fin d → ℝ)} {J K : StateIntervalJet d} {F : StateJetOn s}
    (hF : J.Encloses F) (hn : ∀ x∈s,F.value x≠0) (hcheck : J.inverse=some K) :
    K.Encloses (F.inverse hn) := by
  -- Separate `¬J.value.containsZero` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  by_cases h : ¬J.value.containsZero
  · simp only [inverse,dite_eq_left h,Option.some.injEq] at hcheck
    subst K
    apply encloses_compose hF
    intro x hx
    have hi := IntervalRat.mem_invNonzero (hF x hx).1 (hn x hx) (I := ⟨J.value,h⟩)
    exact ⟨hi,IntervalRat.mem_neg (mem_powerHigh hi 2),by
      simpa only [Rat.cast_ofNat] using IntervalRat.mem_mul (IntervalRat.mem_singleton 2) (mem_powerHigh hi 3)⟩
  · simp [inverse,h] at hcheck

end
end StateIntervalJet
end chebyshev2.Numerics
