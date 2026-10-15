import «2610.05164v2».Numerics.IntervalJet

/-!
Article: 2610.05164v2, Lemma 20.
`«2610.05164v2».Numerics.quadratureCheck_sound` turns finite interval acceptance into the exact
Taylor-integral remainder bound.
Interface: its result can discharge the corresponding enclosure premises of
`«2610.05164v2».Numerics.quadrature_taylor`.
Proof chain: 2610.05164v2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace «2610.05164v2».Numerics
open LeanCert.Core Set
set_option autoImplicit false

/--
Defines `quadratureWeight` of type `ℚ` by `if Even j then 2*h^(j+1)/(j+1) else 0`.

Use: `«2610.05164v2».Numerics.quadratureCheck_sound` rewrites with this definition to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Article: 2610.05164v2, Lemma 20.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadratureWeight (h : ℚ) (j : ℕ) : ℚ :=
  if Even j then 2*h^(j+1)/(j+1) else 0

/--
Defines `quadraturePolynomial` of type `IntervalRat` by `sumIntervals (fun j => roundHigh
(IntervalRat.mul (IntervalRat.singleton (quadratureWeight h j)) (jetAt J j))) (n+1)`.

Use: `«2610.05164v2».Numerics.quadratureCheck_sound` uses this definition to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Article: 2610.05164v2, Lemma 20.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadraturePolynomial (J : IntervalJet) (h : ℚ) (n : ℕ) : IntervalRat :=
  sumIntervals (fun j => roundHigh (IntervalRat.mul (IntervalRat.singleton (quadratureWeight h j))
    (jetAt J j))) (n+1)

/--
Defines `quadratureRadius` of type `ℚ` by `max 0 (2*R*h^(n+2)/(n+2))`.

Use: `«2610.05164v2».Numerics.quadratureCheck_sound` uses this definition to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Article: 2610.05164v2, Lemma 20.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadratureRadius (h R : ℚ) (n : ℕ) : ℚ := max 0 (2*R*h^(n+2)/(n+2))

/--
Defines `quadratureEnclosure` of type `IntervalRat` by `IntervalRat.add (quadraturePolynomial J
h n) ⟨-quadratureRadius h R n,quadratureRadius h R n,neg_le_self (le_max_left _ _)⟩`.

Use: `«2610.05164v2».Numerics.quadratureCheck` uses this definition in the displayed
construction of `quadratureCheck`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 20.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadratureEnclosure (J : IntervalJet) (h R : ℚ) (n : ℕ) : IntervalRat :=
  IntervalRat.add (quadraturePolynomial J h n)
    ⟨-quadratureRadius h R n,quadratureRadius h R n,neg_le_self (le_max_left _ _)⟩

/--
Defines `quadratureCheck` of type `Bool` by `decide (0≤h ∧ 0≤R) && intervalSubsetCheck
(quadratureEnclosure J h R n) output`.

Use: `«2610.05164v2».Numerics.quadratureCheck_sound` uses this definition to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Article: 2610.05164v2, Lemma 20.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def quadratureCheck (J : IntervalJet) (h R : ℚ) (n : ℕ) (output : IntervalRat) : Bool :=
  decide (0≤h ∧ 0≤R) && intervalSubsetCheck (quadratureEnclosure J h R n) output

noncomputable section

/--
Membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 20.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `Even j` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem quadratureCheck_sound {J : IntervalJet} {h R : ℚ} {n : ℕ} {output : IntervalRat}
    (hcheck : quadratureCheck J h R n output=true) {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hpoint : ∀ j<n+1,normalizedDerivative f j c∈jetAt J j)
    (hwhole : ∀ t∈Icc (c-h) (c+h),|normalizedDerivative f (n+1) t|≤R) :
    (∫ t in c-h..c+h,f t)∈output := by
  -- Separate `Even j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hp : (0≤h ∧ 0≤R) ∧ intervalSubsetCheck (quadratureEnclosure J h R n) output=true := by
    simpa only [quadratureCheck,Bool.and_eq_true,decide_eq_true_eq] using hcheck
  have hh : 0≤(h:ℝ) := by exact_mod_cast hp.1.1
  have he := quadrature_taylor_even n hh hf hwhole
  let P := ∑ j∈Finset.range (n+1) with Even j,2*(h:ℝ)^(j+1)/(j+1)*normalizedDerivative f j c
  have hP : P∈quadraturePolynomial J h n := by
    rw [show P=∑ j∈Finset.range (n+1),
      (quadratureWeight h j:ℝ)*normalizedDerivative f j c by
      dsimp [P]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : Even j <;> simp [quadratureWeight,hj]]
    apply mem_sumIntervals
    intro j hj
    exact mem_roundHigh (IntervalRat.mem_mul (IntervalRat.mem_singleton _) (hpoint j hj))
  have hrad : (2:ℝ)*R*(h:ℝ)^(n+2)/(n+2)≤quadratureRadius h R n := by
    have hr : 2*R*h^(n+2)/(n+2)≤quadratureRadius h R n := le_max_right _ _
    exact_mod_cast hr
  have herr : |(∫ t in c-h..c+h,f t)-P|≤quadratureRadius h R n := he.trans hrad
  have hmem : (∫ t in c-h..c+h,f t)-P∈(⟨-quadratureRadius h R n,quadratureRadius h R n,
      neg_le_self (le_max_left _ _)⟩:IntervalRat) := by
    simpa only [IntervalRat.mem_def,Rat.cast_neg] using abs_le.mp herr
  apply intervalSubsetCheck_sound hp.2
  simpa only [quadratureEnclosure,add_sub_cancel] using IntervalRat.mem_add hP hmem

end
end «2610.05164v2».Numerics
