import chebyshev2.Numerics.JetArithmetic
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
Article: chebyshev2, Lemmas 18 and 21.
`chebyshev2.Numerics.reflectJet_Icc_encloses` transfers actual within-derivative jets across
reflected charts with the correct parity.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.FlowStep.check_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
open scoped Pointwise
set_option autoImplicit false

/--
The stated quantitative bound `normalizedWithin (fun t => f (c-t)) s j x=
(-1:ℝ)^j*normalizedWithin f (c+ᵥ -s) j (c-x)`.

Use: `chebyshev2.Numerics.reflectJet_encloses` rewrites with this identity to establish the
stated quantitative bound `JetEncloses (reflectJet J N) (fun t => f (c-t)) s x N`.

Article: chebyshev2, Lemmas 18 and 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedWithin_reflect (f : ℝ → ℝ) (s : Set ℝ) (c x : ℝ) (j : ℕ) :
    normalizedWithin (fun t => f (c-t)) s j x=
      (-1:ℝ)^j*normalizedWithin f (c+ᵥ -s) j (c-x) := by
  simp only [normalizedWithin,iteratedDerivWithin_comp_const_sub,smul_eq_mul]
  ring

/--
Exact identity `c+ᵥ -(Icc a b)=Icc (c-b) (c-a)`.

Use: `chebyshev2.Numerics.reflectJet_Icc_encloses` uses this identity to establish the
stated quantitative bound `JetEncloses (reflectJet J N) (fun t => f (c-t)) (Icc a b) x N`.

Article: chebyshev2, Lemmas 18 and 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem reflect_Icc (a b c : ℝ) : c+ᵥ -(Icc a b)=Icc (c-b) (c-a) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  ext x
  simp only [Set.mem_vadd_set,Set.mem_neg]
  constructor
  · rintro ⟨y,hy,rfl⟩
    change a≤ -y ∧ -y≤b at hy
    change c-b≤c+y ∧ c+y≤c-a
    constructor <;> linarith [hy.1,hy.2]
  · intro hx
    refine ⟨x-c,?_,?_⟩
    · change a≤ -(x-c) ∧ -(x-c)≤b
      constructor <;> linarith [hx.1,hx.2]
    · change c+(x-c)=x
      ring

/--
Exact identity `c+ᵥ -s=(fun x => c-x) '' s`.

Use: `chebyshev2.Numerics.uniqueDiffOn_reflect` rewrites with this identity to establish
the precise assertion is `UniqueDiffOn ℝ (c+ᵥ -s)`.

Article: chebyshev2, Lemmas 18 and 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem reflectSet_eq_image (c : ℝ) (s : Set ℝ) :
    c+ᵥ -s=(fun x => c-x) '' s := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨-y,hy,by change c- -y=c+y;ring⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨-y,by simpa using hy,by change c+-y=c-y;ring⟩

/--
The precise assertion is `UniqueDiffOn ℝ (c+ᵥ -s)`.

Use: `chebyshev2.Numerics.ReferenceJetSource.rightSourceCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses JC (rightCoefficientC R) s x N ∧ JetEncloses JA
(rightCoefficientA R) s x N ∧ JetEncloses JB (rightCoefficientB R sigma) s x N`.

Article: chebyshev2, Lemmas 18 and 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.reflectSet_eq_image` with the
arguments shown in the proof.
-/
theorem uniqueDiffOn_reflect {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (c : ℝ) :
    UniqueDiffOn ℝ (c+ᵥ -s) := by
  rw [reflectSet_eq_image]
  apply hs.image (fun x _ => ((hasDerivWithinAt_id x s).const_sub c).hasFDerivWithinAt)
  intro x hx
  apply Function.Surjective.denseRange
  intro y
  exact ⟨-y,by simp⟩

/--
Defines `reflectJet` of type `IntervalJet` by `tabulateJet N (fun j => if Even j then jetAt J j
else IntervalRat.neg (jetAt J j))`.

Use: `chebyshev2.Numerics.reflectJet_encloses` rewrites with this definition to establish
the stated quantitative bound `JetEncloses (reflectJet J N) (fun t => f (c-t)) s x N`.

Article: chebyshev2, Lemmas 18 and 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def reflectJet (J : IntervalJet) (N : ℕ) : IntervalJet :=
  tabulateJet N (fun j => if Even j then jetAt J j else IntervalRat.neg (jetAt J j))

/--
The stated quantitative bound `JetEncloses (reflectJet J N) (fun t => f (c-t)) s x N`.

Use: `chebyshev2.Numerics.reflectJet_Icc_encloses` uses this identity to establish the
stated quantitative bound `JetEncloses (reflectJet J N) (fun t => f (c-t)) (Icc a b) x N`.

Article: chebyshev2, Lemmas 18 and 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `Even j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem reflectJet_encloses {J : IntervalJet} {f : ℝ → ℝ} {s : Set ℝ}
    {c x : ℝ} {N : ℕ} (hJ : JetEncloses J f (c+ᵥ -s) (c-x) N) :
    JetEncloses (reflectJet J N) (fun t => f (c-t)) s x N := by
  -- Separate `Even j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  intro j hj
  rw [reflectJet,jetAt_tabulateJet hj,normalizedWithin_reflect]
  by_cases he : Even j
  · rw [ite_eq_left he,he.neg_one_pow,one_mul]
    exact hJ j hj
  · rw [ite_eq_right he,(Nat.not_even_iff_odd.mp he).neg_one_pow,neg_one_mul]
    exact IntervalRat.mem_neg (hJ j hj)

/--
The stated quantitative bound `JetEncloses (reflectJet J N) (fun t => f (c-t)) (Icc a b) x N`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemmas 18 and 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.reflectJet_encloses`,
`chebyshev2.Numerics.reflect_Icc` with the arguments shown in the proof.
-/
theorem reflectJet_Icc_encloses {J : IntervalJet} {f : ℝ → ℝ}
    {a b c x : ℝ} {N : ℕ} (hJ : JetEncloses J f (Icc (c-b) (c-a)) (c-x) N) :
    JetEncloses (reflectJet J N) (fun t => f (c-t)) (Icc a b) x N :=
  reflectJet_encloses (by simpa only [reflect_Icc] using hJ)

end chebyshev2.Numerics
