import chebyshev2.Numerics.FlowStepCheck

/-!
Article: chebyshev2, Lemma 21.
`chebyshev2.Numerics.flowChainCheck_sound` composes accepted steps with verified initial
conditions and every seam.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.validated_flow_step`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
set_option autoImplicit false

/--
Defines `flowChainCheck` by pattern matching with result type `List FlowStep → Bool`. The
displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.flowChainCheck_sound` uses this definition to establish
membership in the specified domain/enclosure: `y b∈output`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def flowChainCheck (a b : ℚ) (initial output : IntervalRat) : List FlowStep → Bool
  | [] => decide (a=b) && intervalSubsetCheck initial output
  | W::Ws => decide (a+W.width≤b) && intervalSubsetCheck initial W.initial &&
    W.check && flowChainCheck (a+W.width) b W.output output Ws

/--
Defines `flowChainCoefficients` by pattern matching with result type `List FlowStep → Prop`.
The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.Numerics.flowChainCheck_sound` uses this definition to establish
membership in the specified domain/enclosure: `y b∈output`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
noncomputable def flowChainCoefficients (C A B : ℝ → ℝ) (a : ℚ) : List FlowStep → Prop
  | [] => True
  | W::Ws => W.Coefficients C A B a ∧ flowChainCoefficients C A B (a+W.width) Ws

/--
Membership in the specified domain/enclosure: `y b∈output`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `Ws` while keeping `a initial` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem flowChainCheck_sound {a b : ℚ} {initial output : IntervalRat} {Ws : List FlowStep}
    {C A B y : ℝ → ℝ} (hcheck : flowChainCheck a b initial output Ws=true)
    (hcoeff : flowChainCoefficients C A B a Ws)
    (hy : ContinuousOn y (Icc (a:ℝ) b))
    (hyd : ∀ t∈Ioo (a:ℝ) b,HasDerivAt y (C t+A t*y t+B t*y t^2) t)
    (hy0 : y a∈initial) : y b∈output := by
  -- Induct on `Ws` while keeping `a initial` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction Ws generalizing a initial with
  | nil =>
    have hp : a=b ∧ intervalSubsetCheck initial output=true := by
      simpa only [flowChainCheck,Bool.and_eq_true,decide_eq_true_eq] using hcheck
    rw [hp.1] at hy0
    exact intervalSubsetCheck_sound hp.2 hy0
  | cons W Ws ih =>
    have hp : ((a+W.width≤b ∧ intervalSubsetCheck initial W.initial=true) ∧ W.check=true) ∧
        flowChainCheck (a+W.width) b W.output output Ws=true := by
      simpa only [flowChainCheck,Bool.and_eq_true,decide_eq_true_eq] using hcheck
    have hW := hp.1.2
    have hh : 0<W.width := by
      have hn := hW
      simp only [FlowStep.check,Bool.and_eq_true,decide_eq_true_eq] at hn
      exact hn.1.1.1.1.1
    have hhr : 0<(W.width:ℝ) := by exact_mod_cast hh
    have hab : (a:ℝ)+W.width≤b := by exact_mod_cast hp.1.1.1
    have hsub : Icc (a:ℝ) (a+W.width)⊆Icc (a:ℝ) b := Icc_subset_Icc le_rfl hab
    rcases hcoeff with ⟨⟨hC,hA,hB,hpoint,hwhole⟩,hrest⟩
    have hend := W.check_sound hW hC hA hB hpoint hwhole (hy.mono hsub)
      (fun t ht => hyd t ⟨ht.1,ht.2.trans_le hab⟩)
      (intervalSubsetCheck_sound hp.1.1.2 hy0)
    apply ih hp.2 hrest
    · apply hy.mono
      intro t ht
      simp only [Rat.cast_add] at ht
      exact ⟨by linarith [ht.1],ht.2⟩
    · intro t ht
      simp only [Rat.cast_add] at ht
      exact hyd t ⟨by linarith [ht.1],ht.2⟩
    · simpa only [Rat.cast_add] using hend

end chebyshev2.Numerics
