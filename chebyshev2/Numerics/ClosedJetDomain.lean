import chebyshev2.Numerics.JetArithmetic

/-!
Article: chebyshev2, Lemmas 18–21.
`chebyshev2.Numerics.JetEncloses.rebase` restricts actual closed-domain derivative jets to the
integration step.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.FlowStep.check_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set
open scoped ContDiff
set_option autoImplicit false

/--
Exact identity `iteratedDerivWithin j f s x=iteratedDerivWithin j f t x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemmas 18–21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem iteratedDerivWithin_subset {f : ℝ → ℝ} {s t : Set ℝ} {x : ℝ} {j : ℕ}
    (hsub : s⊆t) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hf : ContDiffOn ℝ j f t) (hx : x∈s) :
    iteratedDerivWithin j f s x=iteratedDerivWithin j f t x := by
  simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [iteratedFDerivWithin_subset hsub hs ht hf hx]

/--
Exact identity `normalizedWithin f s j x=normalizedWithin f t j x`.

Use: `chebyshev2.Numerics.JetEncloses.rebase` rewrites with this identity to establish the
precise assertion is `JetEncloses J f t x N`.

Article: chebyshev2, Lemmas 18–21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_subset {f : ℝ → ℝ} {s t : Set ℝ} {x : ℝ} {j : ℕ}
    (hsub : s⊆t) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hf : ContDiffOn ℝ j f t) (hx : x∈s) :
    normalizedWithin f s j x=normalizedWithin f t j x := by
  simp only [normalizedWithin,iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [iteratedFDerivWithin_subset hsub hs ht hf hx]

/--
The precise assertion is `JetEncloses J f t x N`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemmas 18–21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.normalizedWithin_subset` with the
arguments shown in the proof.
-/
theorem JetEncloses.rebase {J : IntervalJet} {f : ℝ → ℝ} {s t u : Set ℝ} {x : ℝ} {N : ℕ}
    (hJ : JetEncloses J f s x N) (hf : ContDiffOn ℝ ∞ f u)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t) (hu : UniqueDiffOn ℝ u)
    (hsu : s⊆u) (htu : t⊆u) (hxs : x∈s) (hxt : x∈t) : JetEncloses J f t x N := by
  intro j hj
  rw [normalizedWithin_subset htu ht hu (hf.of_le (by simp)) hxt,
    ←normalizedWithin_subset hsu hs hu (hf.of_le (by simp)) hxs]
  exact hJ j hj

end chebyshev2.Numerics
