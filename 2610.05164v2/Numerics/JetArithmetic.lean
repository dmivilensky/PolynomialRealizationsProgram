import «2610.05164v2».Numerics.IntervalJet

/-!
Article: 2610.05164v2, Lemma 18.
`«2610.05164v2».Numerics.reciprocalJetCheck_encloses` proves finite normalized derivative
arithmetic, including checked triangular inverse recurrences.
Interface: its result can discharge the corresponding enclosure premises of
`«2610.05164v2».Numerics.JetExpr.enclose_sound`.
Proof chain: 2610.05164v2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace «2610.05164v2».Numerics
open Set LeanCert.Core
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `JetEncloses` of type `Prop` by `∀ j≤N, normalizedWithin f s j x∈jetAt J j`.

Use: `«2610.05164v2».Numerics.addJet_encloses` uses this definition to establish the stated
quantitative bound `JetEncloses (addJet J K N) (fun t => f t+g t) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def JetEncloses (J : IntervalJet) (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) (N : ℕ) : Prop :=
  ∀ j≤N, normalizedWithin f s j x∈jetAt J j

/--
Defines `jetSubsetCheck` of type `Bool` by `(List.range (N+1)).all (fun j =>
intervalSubsetCheck (jetAt J j) (jetAt K j))`.

Use: `«2610.05164v2».Numerics.jetSubsetCheck_sound` rewrites with this definition to establish
the precise assertion is `JetEncloses K f s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def jetSubsetCheck (J K : IntervalJet) (N : ℕ) : Bool :=
  (List.range (N+1)).all (fun j => intervalSubsetCheck (jetAt J j) (jetAt K j))

/--
The precise assertion is `JetEncloses K f s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.checkCachedInto_sound` uses this assertion to establish
the precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.intervalSubsetCheck_sound` with
the arguments shown in the proof.
-/
theorem jetSubsetCheck_sound {J K : IntervalJet} {N : ℕ}
    (h : jetSubsetCheck J K N=true) {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hJ : JetEncloses J f s x N) : JetEncloses K f s x N := by
  simp only [jetSubsetCheck,List.all_eq_true,List.mem_range] at h
  intro j hj
  exact intervalSubsetCheck_sound (h j (by omega)) (hJ j hj)

/--
Defines `tabulateJet` of type `IntervalJet` by `(List.range (N+1)).map f`.

Use: `«2610.05164v2».Numerics.addJet` uses this definition in the displayed construction of
`addJet`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def tabulateJet (N : ℕ) (f : ℕ → IntervalRat) : IntervalJet :=
  (List.range (N+1)).map f

/--
Exact identity `jetAt (tabulateJet N f) j=f j`.

Use: `«2610.05164v2».Numerics.addJet_encloses` rewrites with this identity to establish the
stated quantitative bound `JetEncloses (addJet J K N) (fun t => f t+g t) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem jetAt_tabulateJet {N j : ℕ} (h : j≤N) (f : ℕ → IntervalRat) :
    jetAt (tabulateJet N f) j=f j := by simp [jetAt,tabulateJet,show j<N+1 by omega]

/--
Defines `constantJet` of type `IntervalJet` by `tabulateJet N (fun j => IntervalRat.singleton
(if j=0 then q else 0))`.

Use: `«2610.05164v2».Numerics.constantJet_encloses` rewrites with this definition to establish
the stated quantitative bound `JetEncloses (constantJet q N) (fun _ => (q:ℝ)) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def constantJet (q : ℚ) (N : ℕ) : IntervalJet :=
  tabulateJet N (fun j => IntervalRat.singleton (if j=0 then q else 0))

/--
Defines `variableJet` of type `IntervalJet` by `tabulateJet N (fun j => if j=0 then I else
IntervalRat.singleton (if j=1 then 1 else 0))`.

Use: `«2610.05164v2».Numerics.variableJet_encloses` rewrites with this definition to establish
the stated quantitative bound `JetEncloses (variableJet I N) (fun t => t) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def variableJet (I : IntervalRat) (N : ℕ) : IntervalJet :=
  tabulateJet N (fun j => if j=0 then I else IntervalRat.singleton (if j=1 then 1 else 0))

/--
Defines `addJet` of type `IntervalJet` by `tabulateJet N (fun j => roundHigh (IntervalRat.add
(jetAt J j) (jetAt K j)))`.

Use: `«2610.05164v2».Numerics.addJet_encloses` rewrites with this definition to establish the
stated quantitative bound `JetEncloses (addJet J K N) (fun t => f t+g t) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def addJet (J K : IntervalJet) (N : ℕ) : IntervalJet :=
  tabulateJet N (fun j => roundHigh (IntervalRat.add (jetAt J j) (jetAt K j)))

/--
Defines `mulJet` of type `IntervalJet` by `tabulateJet N (convolution J K)`.

Use: `«2610.05164v2».Numerics.mulJet_encloses` rewrites with this definition to establish the
stated quantitative bound `JetEncloses (mulJet J K N) (fun t => f t*g t) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def mulJet (J K : IntervalJet) (N : ℕ) : IntervalJet :=
  tabulateJet N (convolution J K)

/--
Defines `squareJet` of type `IntervalJet` by `tabulateJet N (squareConvolution J)`.

Use: `«2610.05164v2».Numerics.squareJet_encloses` rewrites with this definition to establish
the stated quantitative bound `JetEncloses (squareJet J N) (fun t => f t^2) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def squareJet (J : IntervalJet) (N : ℕ) : IntervalJet :=
  tabulateJet N (squareConvolution J)

/--
Defines `negJet` of type `IntervalJet` by `tabulateJet N (fun j => IntervalRat.neg (jetAt J
j))`.

Use: `«2610.05164v2».Numerics.negJet_encloses` rewrites with this definition to establish the
stated quantitative bound `JetEncloses (negJet J N) (fun t => -f t) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def negJet (J : IntervalJet) (N : ℕ) : IntervalJet :=
  tabulateJet N (fun j => IntervalRat.neg (jetAt J j))

/--
The stated quantitative bound `JetEncloses (constantJet q N) (fun _ => (q:ℝ)) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `j=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem constantJet_encloses (q : ℚ) (N : ℕ) (s : Set ℝ) (x : ℝ) :
    JetEncloses (constantJet q N) (fun _ => (q:ℝ)) s x N := by
  intro j hj
  rw [constantJet,jetAt_tabulateJet hj]
  by_cases h : j=0
  · subst j; simpa using IntervalRat.mem_singleton q
  · rw [normalizedWithin_const (Nat.pos_of_ne_zero h),ite_eq_right h]
    simpa using IntervalRat.mem_singleton 0

/--
The stated quantitative bound `JetEncloses (variableJet I N) (fun t => t) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `j=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem variableJet_encloses {I : IntervalRat} {x : ℝ} (hx : x∈I)
    (N : ℕ) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hxs : x∈s) :
    JetEncloses (variableJet I N) (fun t => t) s x N := by
  -- Separate `j=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  intro j hj
  rw [variableJet,jetAt_tabulateJet hj]
  by_cases h0 : j=0
  · subst j; simpa using hx
  · by_cases h1 : j=1
    · subst j
      simp [normalizedWithin,iteratedDerivWithin_fun_id hxs hs,IntervalRat.singleton]
    · simp [normalizedWithin,iteratedDerivWithin_fun_id hxs hs,h0,h1,IntervalRat.singleton]

/--
The stated quantitative bound `JetEncloses (addJet J K N) (fun t => f t+g t) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
`«2610.05164v2».Numerics.normalizedWithin_add`, `«2610.05164v2».Numerics.mem_roundHigh` with
the arguments shown in the proof.
-/
theorem addJet_encloses {J K : IntervalJet} {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ} {N : ℕ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hf : ContDiffWithinAt ℝ N f s x) (hg : ContDiffWithinAt ℝ N g s x)
    (hJ : JetEncloses J f s x N) (hK : JetEncloses K g s x N) :
    JetEncloses (addJet J K N) (fun t => f t+g t) s x N := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
  -- `«2610.05164v2».Numerics.normalizedWithin_add`, `«2610.05164v2».Numerics.mem_roundHigh`
  -- with the arguments shown in the proof.
  intro j hj
  rw [addJet,jetAt_tabulateJet hj,normalizedWithin_add hs hx
    (hf.of_le (by exact_mod_cast hj)) (hg.of_le (by exact_mod_cast hj))]
  exact mem_roundHigh (IntervalRat.mem_add (hJ j hj) (hK j hj))

/--
The stated quantitative bound `JetEncloses (mulJet J K N) (fun t => f t*g t) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.enclose_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
`«2610.05164v2».Numerics.normalizedWithin_mul`, `«2610.05164v2».Numerics.mem_convolution` with
the arguments shown in the proof.
-/
theorem mulJet_encloses {J K : IntervalJet} {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ} {N : ℕ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (hf : ContDiffWithinAt ℝ N f s x) (hg : ContDiffWithinAt ℝ N g s x)
    (hJ : JetEncloses J f s x N) (hK : JetEncloses K g s x N) :
    JetEncloses (mulJet J K N) (fun t => f t*g t) s x N := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
  -- `«2610.05164v2».Numerics.normalizedWithin_mul`, `«2610.05164v2».Numerics.mem_convolution`
  -- with the arguments shown in the proof.
  intro j hj
  rw [mulJet,jetAt_tabulateJet hj,normalizedWithin_mul hs hx
    (hf.of_le (by exact_mod_cast hj)) (hg.of_le (by exact_mod_cast hj))]
  exact mem_convolution j (fun i hi => hJ i (hi.trans hj))
    (fun i hi => hK i (hi.trans hj))

/--
The stated quantitative bound `JetEncloses (squareJet J N) (fun t => f t^2) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.enclose_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
`«2610.05164v2».Numerics.normalizedWithin_mul`, `«2610.05164v2».Numerics.mem_squareConvolution`
with the arguments shown in the proof.
-/
theorem squareJet_encloses {J : IntervalJet} {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ} {N : ℕ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s) (hf : ContDiffWithinAt ℝ N f s x)
    (hJ : JetEncloses J f s x N) : JetEncloses (squareJet J N) (fun t => f t^2) s x N := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
  -- `«2610.05164v2».Numerics.normalizedWithin_mul`,
  -- `«2610.05164v2».Numerics.mem_squareConvolution` with the arguments shown in the proof.
  intro j hj
  rw [squareJet,jetAt_tabulateJet hj]
  have he := normalizedWithin_mul hs hx (hf.of_le (by exact_mod_cast hj))
    (hf.of_le (by exact_mod_cast hj))
  simp only [← pow_two] at he
  rw [he]
  exact mem_squareConvolution j (fun i hi => hJ i (hi.trans hj))

/--
The stated quantitative bound `JetEncloses (negJet J N) (fun t => -f t) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
`«2610.05164v2».Numerics.normalizedWithin_const_mul` with the arguments shown in the proof.
-/
theorem negJet_encloses {J : IntervalJet} {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ} {N : ℕ}
    (hJ : JetEncloses J f s x N) :
    JetEncloses (negJet J N) (fun t => -f t) s x N := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.jetAt_tabulateJet`,
  -- `«2610.05164v2».Numerics.normalizedWithin_const_mul` with the arguments shown in the
  -- proof.
  intro j hj
  rw [negJet,jetAt_tabulateJet hj]
  have he := normalizedWithin_const_mul f s j (-1) x
  simp only [neg_one_mul] at he
  rw [he]
  exact IntervalRat.mem_neg (hJ j hj)

/--
Defines `reciprocalJetStep` of type `Option IntervalRat` by `if h : ¬(jetAt F 0).containsZero
then some (roundHigh (IntervalRat.mul (IntervalRat.neg (sumIntervals (fun i => roundHigh
(IntervalRat.mul (jetAt F (i+1)) (jetAt R (j-(i+1))))) j)) (IntervalRat.invNonzero ⟨jetAt F
0,h⟩))) else none`.

Use: `«2610.05164v2».Numerics.reciprocalJetCheck` uses this definition in the displayed
construction of `reciprocalJetCheck`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def reciprocalJetStep (F R : IntervalJet) (j : ℕ) : Option IntervalRat :=
  if h : ¬(jetAt F 0).containsZero then
    some (roundHigh (IntervalRat.mul (IntervalRat.neg (sumIntervals
      (fun i => roundHigh (IntervalRat.mul (jetAt F (i+1)) (jetAt R (j-(i+1))))) j))
      (IntervalRat.invNonzero ⟨jetAt F 0,h⟩)))
  else none

/--
Defines `reciprocalJetCheck` of type `Bool` by `if h : ¬(jetAt F 0).containsZero then
intervalSubsetCheck (IntervalRat.invNonzero ⟨jetAt F 0,h⟩) (jetAt R 0) && (List.range N).all
(fun i => match reciprocalJetStep F R (i+1) with | none => false | some I =>
intervalSubsetCheck I (jetAt R (i+1))) else false`.

Use: `«2610.05164v2».Numerics.reciprocalJetCheck_encloses` rewrites with this definition to
establish the stated quantitative bound `JetEncloses R (fun t => (f t)⁻¹) s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def reciprocalJetCheck (F R : IntervalJet) (N : ℕ) : Bool :=
  if h : ¬(jetAt F 0).containsZero then
    intervalSubsetCheck (IntervalRat.invNonzero ⟨jetAt F 0,h⟩) (jetAt R 0) &&
      (List.range N).all (fun i => match reciprocalJetStep F R (i+1) with
        | none => false
        | some I => intervalSubsetCheck I (jetAt R (i+1)))
  else false

/--
The stated quantitative bound `JetEncloses R (fun t => (f t)⁻¹) s x N`.

Use: `«2610.05164v2».Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Lemma 18.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `j`; the recursive step uses the previous-stage assertion. Separate `¬(jetAt F
0).containsZero` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem reciprocalJetCheck_encloses {F R : IntervalJet} {N : ℕ}
    (hcheck : reciprocalJetCheck F R N=true)
    {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s) (hf : ContDiffWithinAt ℝ N f s x)
    (hn : ∀ t∈s,f t≠0) (hF : JetEncloses F f s x N) :
    JetEncloses R (fun t => (f t)⁻¹) s x N := by
  -- Induct on `j`; the recursive step uses the previous-stage assertion.
  by_cases h : ¬(jetAt F 0).containsZero
  · simp only [reciprocalJetCheck,dite_eq_left h,Bool.and_eq_true,
      List.all_eq_true,List.mem_range] at hcheck
    have hbase : f x∈jetAt F 0 := by simpa using hF 0 (Nat.zero_le _)
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      cases j with
      | zero =>
        simp only [normalizedWithin_zero]
        exact intervalSubsetCheck_sound hcheck.1 (IntervalRat.mem_invNonzero hbase (hn x hx))
      | succ j =>
        have hstep := hcheck.2 j (by omega)
        simp only [reciprocalJetStep,dite_eq_left h] at hstep
        apply intervalSubsetCheck_sound hstep
        rw [normalizedWithin_inverse (by omega) hs hx (hf.of_le (by exact_mod_cast hj)) hn]
        apply mem_roundHigh
        rw [div_eq_mul_inv]
        apply IntervalRat.mem_mul
        · apply IntervalRat.mem_neg
          apply mem_sumIntervals
          intro i hi
          exact mem_roundHigh (IntervalRat.mem_mul (hF (i+1) (by omega))
            (ih (j+1-(i+1)) (by omega) (by omega)))
        · exact IntervalRat.mem_invNonzero hbase (hn x hx)
  · simp [reciprocalJetCheck,h] at hcheck

end «2610.05164v2».Numerics
