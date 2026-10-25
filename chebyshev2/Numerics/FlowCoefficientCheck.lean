import chebyshev2.Numerics.FlowChain
import chebyshev2.Numerics.JetArithmetic

/-!
Article: chebyshev2, Lemma 21.
`chebyshev2.Numerics.flowCoefficientCheck_sound` discharges the actual coefficient-jet premises
before accepting a flow step.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.FlowStep.check_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
open scoped ContDiff
set_option autoImplicit false

/--
Defines `CoefficientCheck` of type `` by `IntervalRat → ℕ → IntervalJet → IntervalJet →
IntervalJet → Bool`.

Use: `chebyshev2.Numerics.flowCoefficientCheck` uses this definition in the displayed
construction of `flowCoefficientCheck`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
abbrev CoefficientCheck := IntervalRat → ℕ → IntervalJet → IntervalJet → IntervalJet → Bool

/--
Defines `flowCoefficientCheck` of type `Bool` by `if hh : 0<W.width then decide (l≤a ∧
a+W.width≤u) && P (IntervalRat.singleton a) (W.order-1) W.pointC W.pointA W.pointB && H
⟨a,a+W.width,by linarith⟩ W.order W.wholeC W.wholeA W.wholeB else false`.

Use: `chebyshev2.Numerics.flowCoefficientCheck_domain` rewrites with this definition to
establish the stated quantitative bound `0<W.width ∧ l≤a ∧ a+W.width≤u`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def flowCoefficientCheck (P H : CoefficientCheck) (a : ℚ) (W : FlowStep) (l : ℚ := 0) (u : ℚ := 1) : Bool :=
  if hh : 0<W.width then
    decide (l≤a ∧ a+W.width≤u) &&
      P (IntervalRat.singleton a) (W.order-1) W.pointC W.pointA W.pointB &&
      H ⟨a,a+W.width,by linarith⟩ W.order W.wholeC W.wholeA W.wholeB
  else false

/--
The stated quantitative bound `0<W.width ∧ l≤a ∧ a+W.width≤u`.

Use: `chebyshev2.Numerics.flowCoefficientCheck_sound` uses this bound to establish the
precise assertion is `W.Coefficients c b d a`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `0<W.width` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem flowCoefficientCheck_domain {P H : CoefficientCheck} {a l u : ℚ} {W : FlowStep}
    (hc : flowCoefficientCheck P H a W l u=true) : 0<W.width ∧ l≤a ∧ a+W.width≤u := by
  by_cases hh : 0<W.width
  · simp only [flowCoefficientCheck,dite_eq_left hh,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact ⟨hh,hc.1.1⟩
  · simp [flowCoefficientCheck,hh] at hc

/--
The precise assertion is `W.Coefficients c b d a`.

Use: `chebyshev2.Numerics.ReferenceJetSource.rightFlowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (rightCoefficientC R)
(rightCoefficientA R) (rightCoefficientB R sigma) a`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.flowCoefficientCheck_domain` with
the arguments shown in the proof.
-/
theorem flowCoefficientCheck_sound {P H : CoefficientCheck} {a l u : ℚ} {W : FlowStep}
    {c b d : ℝ → ℝ}
    (hsrc : ∀ Q∈[P,H],∀ {X N JC JA JB},Q X N JC JA JB=true →
      ∀ {s : Set ℝ},UniqueDiffOn ℝ s → s⊆Icc (l:ℝ) u →
      ∀ {x : ℝ},x∈s → x∈X →
        JetEncloses JC c s x N ∧ JetEncloses JA b s x N ∧ JetEncloses JB d s x N)
    (hc : ContDiffOn ℝ ∞ c (Icc (l:ℝ) u))
    (hb : ContDiffOn ℝ ∞ b (Icc (l:ℝ) u))
    (hd : ContDiffOn ℝ ∞ d (Icc (l:ℝ) u))
    (hcheck : flowCoefficientCheck P H a W l u=true) : W.Coefficients c b d a := by
  -- Use the identities/estimates `chebyshev2.Numerics.flowCoefficientCheck_domain` with
  -- the arguments shown in the proof.
  obtain ⟨hh,ha,hend⟩ := flowCoefficientCheck_domain hcheck
  have hp := hcheck
  simp only [flowCoefficientCheck,dite_eq_left hh,Bool.and_eq_true,decide_eq_true_eq] at hp
  have har : (l:ℝ)≤a := by exact_mod_cast ha
  have hbr : (a:ℝ)+W.width≤u := by exact_mod_cast hend
  have hhr : (0:ℝ)<W.width := by exact_mod_cast hh
  have hsub : Icc (a:ℝ) (a+W.width)⊆Icc (l:ℝ) u := Icc_subset_Icc har hbr
  have hs : UniqueDiffOn ℝ (Icc (a:ℝ) (a+W.width)) := uniqueDiffOn_Icc (by linarith)
  refine ⟨(hc.mono hsub).of_le (by simp),(hb.mono hsub).of_le (by simp),
    (hd.mono hsub).of_le (by simp),?_,?_⟩
  · intro j hj
    have h := hsrc P (by simp) hp.1.2 hs hsub
      (show (a:ℝ)∈Icc (a:ℝ) (a+W.width) from ⟨le_rfl,by linarith⟩)
      (IntervalRat.mem_singleton a)
    exact ⟨h.1 j (by omega),h.2.1 j (by omega),h.2.2 j (by omega)⟩
  · intro t ht j hj
    have h := hsrc H (by simp) hp.2 hs hsub ht
      (show t∈(⟨a,a+W.width,by linarith⟩:IntervalRat) by
        simpa only [IntervalRat.mem_def,Rat.cast_add,Set.mem_Icc] using ht)
    exact ⟨h.1 j (by omega),h.2.1 j (by omega),h.2.2 j (by omega)⟩

end chebyshev2.Numerics
