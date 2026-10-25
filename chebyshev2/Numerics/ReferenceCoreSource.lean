import chebyshev2.Numerics.OpenJetExpr
import chebyshev2.DualCertificate.ReferenceNumericalIntegrands

/-!
Article: chebyshev2, Lemma 16; formula (34).
`chebyshev2.Numerics.ReferenceCoreSource.sourceCheck_sound` bounds the actual reference
contact-integral source for the general jet-based quadrature interface.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.quadratureCheck_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics.ReferenceCoreSource
open Set LeanCert.Core chebyshev2.Calibration
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2000000

/--
Defines `env` by pattern matching with result type `ℕ → ℝ → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.ReferenceCoreSource.core_regular` rewrites with this definition
to establish `(core W).Regular (env R hσ) s`.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
noncomputable def env (R : ReferenceData) {σ : ℝ} (hσ : 0<σ) : ℕ → ℝ → ℝ
  | 0 => R.normalizedFilter hσ
  | 1 => R.normalizedReflectedFilter hσ
  | 2 => R.normalizedGamma hσ
  | _ => R.normalizedVelocity

/--
Defines `inputs` by pattern matching with result type `ℕ → IntervalJet`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.ReferenceCoreSource.sourceCheck` uses this definition in the
displayed construction of `sourceCheck`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def inputs (JL JR JG JP : IntervalJet) : ℕ → IntervalJet
  | 0 => JL
  | 1 => JR
  | 2 => JG
  | _ => JP

/--
Defines `q` of type `OpenJetExpr` by `.mul (.square .variable (W 0)) .variable (W 1)`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.Q` uses this definition in the displayed
construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def q (W : ℕ → IntervalJet) : OpenJetExpr :=
  .mul (.square .variable (W 0)) .variable (W 1)
/--
Defines `Q` of type `OpenJetExpr` by `.mul (q W) (.add (.literal 2) (.neg (q W) (W 2)) (W 3))
(W 4)`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.core` uses this definition in the displayed
construction of `core`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def Q (W : ℕ → IntervalJet) : OpenJetExpr :=
  .mul (q W) (.add (.literal 2) (.neg (q W) (W 2)) (W 3)) (W 4)
/--
Defines `core` of type `OpenJetExpr` by `.mul (.add (.add (.mul (.literal 2) (.mul (Q W)
(.input 2) (W 5)) (W 6)) (.neg (.square (.input 0) (W 7)) (W 8)) (W 9)) (.neg (.square (.input
1) (W 10)) (W 11)) (W 12)) (.input 3) (W 13)`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.core_regular` rewrites with this definition
to establish `(core W).Regular (env R hσ) s`.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def core (W : ℕ → IntervalJet) : OpenJetExpr :=
  .mul (.add (.add (.mul (.literal 2) (.mul (Q W) (.input 2) (W 5)) (W 6))
    (.neg (.square (.input 0) (W 7)) (W 8)) (W 9))
    (.neg (.square (.input 1) (W 10)) (W 11)) (W 12)) (.input 3) (W 13)

/--
Exact identity `(core W).value (env R hσ) t=R.contactCoreIntegrand hσ t`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.sourceCheck_sound` uses this identity to
establish the precise assertion is `JetEncloses J (R.contactCoreIntegrand hσ) s x n`.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem core_value (R : ReferenceData) {σ : ℝ} (hσ : 0<σ)
    (W : ℕ → IntervalJet) (t : ℝ) :
    (core W).value (env R hσ) t=R.contactCoreIntegrand hσ t := by
  simp only [core,Q,q,OpenJetExpr.value,env,ReferenceData.contactCoreIntegrand,id_eq,Rat.cast_ofNat]
  ring

/--
The precise assertion is `(core W).Regular (env R hσ) s`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.sourceCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses J (R.contactCoreIntegrand hσ) s x n`.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedFilter_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedGamma_smooth` with the arguments shown in
the proof.
-/
theorem core_regular (R : ReferenceData) {σ : ℝ} (hσ : 0<σ)
    (W : ℕ → IntervalJet) {s : Set ℝ} (hsub : s⊆Icc (0:ℝ) 1) :
    (core W).Regular (env R hσ) s := by
  have hl := (R.normalizedFilter_smooth hσ).mono hsub
  have hr := (R.normalizedReflectedFilter_smooth hσ).mono hsub
  have hg := (R.normalizedGamma_smooth hσ).mono hsub
  have hp := R.normalizedVelocity_smooth.mono hsub
  simp [core,Q,q,OpenJetExpr.Regular,env,hl,hr,hg,hp]

/--
Defines `sourceCheck` of type `Bool` by `(core W).check (inputs JL JR JG JP) X n &&
jetSubsetCheck (W 13) J n`.

Use: `chebyshev2.Numerics.ReferenceCoreSource.sourceCheck_sound` rewrites with this
definition to establish `JetEncloses J (R.contactCoreIntegrand hσ) s x
n`.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def sourceCheck (W : ℕ → IntervalJet) (JL JR JG JP : IntervalJet)
    (X : IntervalRat) (n : ℕ) (J : IntervalJet) : Bool :=
  (core W).check (inputs JL JR JG JP) X n && jetSubsetCheck (W 13) J n

/--
The precise assertion is `JetEncloses J (R.contactCoreIntegrand hσ) s x n`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16; formula (34).

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sourceCheck_sound (R : ReferenceData) {σ : ℝ} (hσ : 0<σ)
    {W : ℕ → IntervalJet} {JL JR JG JP J : IntervalJet} {X : IntervalRat} {n : ℕ}
    (hc : sourceCheck W JL JR JG JP X n J=true)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hsub : s⊆Icc (0:ℝ) 1)
    {x : ℝ} (hx : x∈s) (hX : x∈X)
    (hL : JetEncloses JL (R.normalizedFilter hσ) s x n)
    (hR : JetEncloses JR (R.normalizedReflectedFilter hσ) s x n)
    (hG : JetEncloses JG (R.normalizedGamma hσ) s x n)
    (hP : JetEncloses JP R.normalizedVelocity s x n) :
    JetEncloses J (R.contactCoreIntegrand hσ) s x n := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  simp only [sourceCheck,Bool.and_eq_true] at hc
  have hi : ∀ i,JetEncloses (inputs JL JR JG JP i) (env R hσ i) s x n := by
    intro i
    match i with
    | 0 => exact hL
    | 1 => exact hR
    | 2 => exact hG
    | _+3 => exact hP
  have h := jetSubsetCheck_sound hc.2 (OpenJetExpr.check_sound hs hx hX hi
    (core W) (core_regular R hσ W hsub) hc.1)
  have he := funext (core_value R hσ W)
  rw [he] at h
  exact h

end chebyshev2.Numerics.ReferenceCoreSource
