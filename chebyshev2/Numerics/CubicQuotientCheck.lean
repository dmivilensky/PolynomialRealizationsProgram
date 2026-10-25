import chebyshev2.Numerics.ClosedJetDomain
import chebyshev2.Calculus.RemovingCubicZero

/-!
Article: chebyshev2, Lemma 22.
`chebyshev2.Numerics.cubicQuotientCheck_sound` transfers the actual cubic-zero removal theorem
to a finite interval-jet enclosure.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Calculus.removing_cubic_zero`.
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
Defines `cubicQuotientEnclosure` of type `IntervalRat` by `roundHigh (IntervalRat.add
(sumIntervals (fun l => roundHigh (IntervalRat.mul (IntervalRat.mul (IntervalRat.singleton
((j+l).choose j)) (jetAt P (j+l+3))) (powerHigh T l))) (N-j+1)) (IntervalRat.mul
(IntervalRat.mul (IntervalRat.singleton ((N+1).choose j)) (powerHigh T (N+1-j))) R))`.

Use: `chebyshev2.Numerics.cubicQuotientCheck` uses this definition in the displayed
construction of `cubicQuotientCheck`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 22.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def cubicQuotientEnclosure (P : IntervalJet) (R T : IntervalRat) (N j : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.add
    (sumIntervals (fun l => roundHigh (IntervalRat.mul
      (IntervalRat.mul (IntervalRat.singleton ((j+l).choose j)) (jetAt P (j+l+3)))
      (powerHigh T l))) (N-j+1))
    (IntervalRat.mul (IntervalRat.mul (IntervalRat.singleton ((N+1).choose j))
      (powerHigh T (N+1-j))) R))

/--
Defines `cubicQuotientCheck` of type `Bool` by `(List.range (N+1)).all (fun j =>
intervalSubsetCheck (cubicQuotientEnclosure P R T N j) (jetAt G j))`.

Use: `chebyshev2.Numerics.cubicQuotientCheck_self` rewrites with this definition to
establish acceptance/decoding identity for the displayed finite data: `cubicQuotientCheck P R T
N (tabulateJet N (cubicQuotientEnclosure P R T N))=true`.

Article: chebyshev2, Lemma 22.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def cubicQuotientCheck (P : IntervalJet) (R T : IntervalRat) (N : ℕ) (G : IntervalJet) : Bool :=
  (List.range (N+1)).all (fun j => intervalSubsetCheck (cubicQuotientEnclosure P R T N j) (jetAt G j))

/--
Acceptance/decoding identity for the displayed finite data: `cubicQuotientCheck P R T N
(tabulateJet N (cubicQuotientEnclosure P R T N))=true`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 22.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.jetAt_tabulateJet` with the
arguments shown in the proof.
-/
theorem cubicQuotientCheck_self (P : IntervalJet) (R T : IntervalRat) (N : ℕ) :
    cubicQuotientCheck P R T N (tabulateJet N (cubicQuotientEnclosure P R T N))=true := by
  simp only [cubicQuotientCheck,List.all_eq_true,List.mem_range]
  intro j hj
  rw [jetAt_tabulateJet (by omega)]
  simp [intervalSubsetCheck]

/--
Pointwise equality on the specified domain: `EqOn g h (Icc 0 β)`.

Use: `chebyshev2.Numerics.cubicQuotientCheck_sound` uses this pointwise identity to
establish the precise assertion is `JetEncloses G g (Icc 0 β) t N`.

Article: chebyshev2, Lemma 22.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem cubic_quotient_unique {β : ℝ} (hβ : 0<β) {f g h : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 β)) (hh : ContinuousOn h (Icc 0 β))
    (hfg : ∀ t∈Icc 0 β,f t=t^3*g t) (hfh : ∀ t∈Icc 0 β,f t=t^3*h t) :
    EqOn g h (Icc 0 β) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have he : EqOn g h (Ioc 0 β) := by
    intro t ht
    exact mul_left_cancel₀ (pow_ne_zero 3 ht.1.ne')
      ((hfg t ⟨ht.1.le,ht.2⟩).symm.trans (hfh t ⟨ht.1.le,ht.2⟩))
  exact he.of_subset_closure hg hh Ioc_subset_Icc_self (by rw [closure_Ioc hβ.ne])

/--
The precise assertion is `JetEncloses G g (Icc 0 β) t N`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 22.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Calculus.removing_cubic_zero`,
`chebyshev2.Numerics.cubic_quotient_unique`,
`chebyshev2.Numerics.normalizedWithin_congr` with the arguments shown in the proof.
-/
theorem cubicQuotientCheck_sound {β : ℝ} (hβ : 0<β) {f g : ℝ → ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ (N+4) f (Icc 0 β)) (hg : ContinuousOn g (Icc 0 β))
    (hfactor : ∀ t∈Icc 0 β,f t=t^3*g t)
    (h₀ : f 0=0) (h₁ : derivWithin f (Icc 0 β) 0=0)
    (h₂ : iteratedDerivWithin 2 f (Icc 0 β) 0=0)
    {P G : IntervalJet} {R T : IntervalRat}
    (hc : cubicQuotientCheck P R T N G=true)
    (hP : ∀ j≤N+3,normalizedWithin f (Icc 0 β) j 0∈jetAt P j)
    (hR : ∀ z∈Icc 0 β,normalizedWithin f (Icc 0 β) (N+4) z∈R)
    {t : ℝ} (ht : t∈Icc 0 β) (hT : t∈T) : JetEncloses G g (Icc 0 β) t N := by
  -- Use the identities/estimates `chebyshev2.Calculus.removing_cubic_zero`,
  -- `chebyshev2.Numerics.cubic_quotient_unique`,
  -- `chebyshev2.Numerics.normalizedWithin_congr` with the arguments shown in the proof.
  obtain ⟨q,hq,hfq,_,hTaylor⟩ := chebyshev2.Calculus.removing_cubic_zero hβ N hf h₀ h₁ h₂
  have heq := cubic_quotient_unique hβ hg hq.continuousOn hfactor hfq
  simp only [cubicQuotientCheck,List.all_eq_true,List.mem_range] at hc
  intro j hj
  rw [normalizedWithin_congr heq j ht]
  obtain ⟨r,hr,he⟩ := hTaylor j hj t ht R.lo R.hi hR
  change normalizedWithin q (Icc 0 β) j t=_ at he
  rw [he]
  apply intervalSubsetCheck_sound (hc j (by omega))
  apply mem_roundHigh
  apply IntervalRat.mem_add
  · apply mem_sumIntervals
    intro l hl
    apply mem_roundHigh
    apply IntervalRat.mem_mul _ (mem_powerHigh hT l)
    exact IntervalRat.mem_mul (by simpa only [Rat.cast_natCast] using
      (IntervalRat.mem_singleton (((j+l).choose j):ℚ))) (hP (j+l+3) (by omega))
  · exact IntervalRat.mem_mul (IntervalRat.mem_mul (by simpa only [Rat.cast_natCast] using
      (IntervalRat.mem_singleton (((N+1).choose j):ℚ))) (mem_powerHigh hT (N+1-j))) hr

end chebyshev2.Numerics
