import chebyshev2.Numerics.ClosedQuadrature
import chebyshev2.Numerics.JetArithmetic

/-!
Article: chebyshev2, Lemma 20.
`chebyshev2.Numerics.quadratureJetEnclosure_sound` supplies the actual derivative bounds needed
by centered quadrature.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.quadratureCheck_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
set_option autoImplicit false

/--
Defines `intervalAbsBound` of type `ℚ` by `max |I.lo| |I.hi|`.

Use: `chebyshev2.Numerics.intervalAbsBound_sound` uses this definition to establish the
stated quantitative bound `|x|≤(intervalAbsBound I:ℝ)`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def intervalAbsBound (I : IntervalRat) : ℚ := max |I.lo| |I.hi|

/--
The stated quantitative bound `0≤ intervalAbsBound I`.

Use: `chebyshev2.Numerics.quadratureJetCheck` rewrites with this bound to establish
acceptance/decoding identity for the displayed finite data: `quadratureCheck point h
(intervalAbsBound (jetAt whole (n+1))) n (quadratureJetEnclosure point whole h n)=true`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem intervalAbsBound_nonneg (I : IntervalRat) : 0≤ intervalAbsBound I :=
  (abs_nonneg I.lo).trans (le_max_left _ _)

/--
The stated quantitative bound `|x|≤(intervalAbsBound I:ℝ)`.

Use: `chebyshev2.Numerics.quadratureJetEnclosure_sound` uses this bound to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureJetEnclosure
point whole h n`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem intervalAbsBound_sound {I : IntervalRat} {x : ℝ} (hx : x∈I) :
    |x|≤(intervalAbsBound I:ℝ) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  rw [abs_le]
  have hlo : -(intervalAbsBound I:ℝ)≤(I.lo:ℝ) := by
    have h : -intervalAbsBound I≤I.lo := (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
    exact_mod_cast h
  have hhi : (I.hi:ℝ)≤(intervalAbsBound I:ℝ) := by
    have h : I.hi≤ intervalAbsBound I := (le_abs_self _).trans (le_max_right _ _)
    exact_mod_cast h
  exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩

/--
Defines `quadratureJetEnclosure` of type `IntervalRat` by `quadratureEnclosure point h
(intervalAbsBound (jetAt whole (n+1))) n`.

Use: `chebyshev2.Numerics.quadratureJetCheck` rewrites with this definition to establish
acceptance/decoding identity for the displayed finite data: `quadratureCheck point h
(intervalAbsBound (jetAt whole (n+1))) n (quadratureJetEnclosure point whole h n)=true`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadratureJetEnclosure (point whole : IntervalJet) (h : ℚ) (n : ℕ) : IntervalRat :=
  quadratureEnclosure point h (intervalAbsBound (jetAt whole (n+1))) n

 /--
Acceptance/decoding identity for the displayed finite data: `quadratureCheck point h
(intervalAbsBound (jetAt whole (n+1))) n (quadratureJetEnclosure point whole h n)=true`.

Use: `chebyshev2.Numerics.quadratureJetEnclosure_sound` uses this identity to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureJetEnclosure
point whole h n`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem quadratureJetCheck {point whole : IntervalJet} {h : ℚ} (hh : 0≤h) (n : ℕ) :
    quadratureCheck point h (intervalAbsBound (jetAt whole (n+1))) n
      (quadratureJetEnclosure point whole h n)=true := by simp [quadratureCheck,quadratureJetEnclosure,hh,intervalAbsBound_nonneg,intervalSubsetCheck]

 /--
Membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureJetEnclosure
point whole h n`.

Use: `chebyshev2.Numerics.quadratureBestEnclosure_sound` uses this assertion to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureBestEnclosure
point whole h n`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.quadratureCheck_sound_closed`,
`chebyshev2.Numerics.quadratureJetCheck`, `chebyshev2.Numerics.intervalAbsBound_sound`
with the arguments shown in the proof.
-/
theorem quadratureJetEnclosure_sound {point whole : IntervalJet} {h : ℚ} (hh : 0≤h)
    {n : ℕ} {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hpoint : JetEncloses point f (Icc (c-h) (c+h)) c (n+1))
    (hwhole : ∀ t∈Icc (c-h) (c+h),JetEncloses whole f (Icc (c-h) (c+h)) t (n+1)) :
    (∫ t in c-h..c+h,f t)∈quadratureJetEnclosure point whole h n := by
  -- Use the identities/estimates `chebyshev2.Numerics.quadratureCheck_sound_closed`,
  -- `chebyshev2.Numerics.quadratureJetCheck`,
  -- `chebyshev2.Numerics.intervalAbsBound_sound` with the arguments shown in the proof.
  apply quadratureCheck_sound_closed (quadratureJetCheck hh n) hf
  · intro j hj
    exact hpoint j (by omega)
  · intro t ht
    exact intervalAbsBound_sound (hwhole t ht (n+1) le_rfl)

end chebyshev2.Numerics
