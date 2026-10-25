import chebyshev2.Numerics.JetArithmetic
import chebyshev2.Numerics.CubicJet

/-!
Article: chebyshev2, Lemma 18.
`chebyshev2.Numerics.cubicJetCheck_encloses` checks implicit positive-cubic normalized
derivative recurrences.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.JetExpr.enclose_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Defines `centeredSquareJet` of type `IntervalRat` by `sumIntervals (fun i => if i+1=n-i then
squareHigh (jetAt Z (i+1)) else roundHigh (IntervalRat.mul (jetAt Z (i+1)) (jetAt Z (n-i))))
n`.

Use: `chebyshev2.Numerics.centeredCubeJet` uses this definition in the displayed
construction of `centeredCubeJet`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def centeredSquareJet (Z : IntervalJet) (n : ℕ) : IntervalRat :=
  sumIntervals (fun i => if i+1=n-i then squareHigh (jetAt Z (i+1))
    else roundHigh (IntervalRat.mul (jetAt Z (i+1)) (jetAt Z (n-i)))) n

/--
Defines `centeredCubeJet` of type `IntervalRat` by `sumIntervals (fun i => roundHigh
(IntervalRat.mul (jetAt Z (i+1)) (centeredSquareJet Z (n-i-1)))) n`.

Use: `chebyshev2.Numerics.cubicJetNumerator` uses this definition in the displayed
construction of `cubicJetNumerator`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def centeredCubeJet (Z : IntervalJet) (n : ℕ) : IntervalRat :=
  sumIntervals (fun i => roundHigh (IntervalRat.mul (jetAt Z (i+1))
    (centeredSquareJet Z (n-i-1)))) n

/--
Defines `cubicJetNumerator` of type `IntervalRat` by `roundHigh (IntervalRat.sub
(IntervalRat.sub (IntervalRat.add (jetAt B (n+1)) (sumIntervals (fun i => roundHigh
(IntervalRat.mul (jetAt A (i+1)) (jetAt Z (n-i)))) (n+1))) (IntervalRat.mul (IntervalRat.mul
(IntervalRat.singleton 3) (jetAt Z 0)) (centeredSquareJet Z n))) (centeredCubeJet Z n))`.

Use: `chebyshev2.Numerics.cubicJetStep` uses this definition in the displayed construction
of `cubicJetStep`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def cubicJetNumerator (A B Z : IntervalJet) (n : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.sub (IntervalRat.sub
    (IntervalRat.add (jetAt B (n+1)) (sumIntervals (fun i => roundHigh
      (IntervalRat.mul (jetAt A (i+1)) (jetAt Z (n-i)))) (n+1)))
    (IntervalRat.mul (IntervalRat.mul (IntervalRat.singleton 3) (jetAt Z 0))
      (centeredSquareJet Z n))) (centeredCubeJet Z n))

/--
Defines `cubicJetSlope` of type `IntervalRat` by `roundHigh (IntervalRat.add (IntervalRat.mul
(IntervalRat.singleton 2) (jetAt A 0)) (IntervalRat.mul (IntervalRat.mul (IntervalRat.singleton
3) (jetAt B 0)) (inverseHigh (jetAt Z 0))))`.

Use: `chebyshev2.Numerics.cubicJetCheck` uses this definition in the displayed construction
of `cubicJetCheck`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def cubicJetSlope (A B Z : IntervalJet) : IntervalRat :=
  roundHigh (IntervalRat.add (IntervalRat.mul (IntervalRat.singleton 2) (jetAt A 0))
    (IntervalRat.mul (IntervalRat.mul (IntervalRat.singleton 3) (jetAt B 0))
      (inverseHigh (jetAt Z 0))))

/--
Defines `cubicJetStep` of type `IntervalRat` by `roundHigh (IntervalRat.mul (cubicJetNumerator
A B Z n) (inverseHigh (cubicJetSlope A B Z)))`.

Use: `chebyshev2.Numerics.cubicJetCheck` uses this definition in the displayed construction
of `cubicJetCheck`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def cubicJetStep (A B Z : IntervalJet) (n : ℕ) : IntervalRat :=
  roundHigh (IntervalRat.mul (cubicJetNumerator A B Z n) (inverseHigh (cubicJetSlope A B Z)))

/--
Defines `cubicJetCheck` of type `Bool` by `cubicBracketCheck (jetAt A 0) (jetAt B 0) (jetAt Z
0) && decide (0<(jetAt Z 0).lo ∧ 0<(cubicJetSlope A B Z).lo) && (List.range N).all (fun n =>
intervalSubsetCheck (cubicJetStep A B Z n) (jetAt Z (n+1)))`.

Use: `chebyshev2.Numerics.cubicJetCheck_encloses` uses this definition to establish the
stated quantitative bound `JetEncloses Z (fun t => positiveCubic (a t) (b t)) s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def cubicJetCheck (A B Z : IntervalJet) (N : ℕ) : Bool :=
  cubicBracketCheck (jetAt A 0) (jetAt B 0) (jetAt Z 0) &&
    decide (0<(jetAt Z 0).lo ∧ 0<(cubicJetSlope A B Z).lo) &&
    (List.range N).all (fun n => intervalSubsetCheck (cubicJetStep A B Z n) (jetAt Z (n+1)))

/--
Membership in the specified domain/enclosure: `(∑ i∈Finset.range n,z (i+1)*z
(n-i))∈centeredSquareJet Z n`.

Use: `chebyshev2.Numerics.mem_centeredCubeJet` uses this assertion to establish membership
in the specified domain/enclosure: `(∑ i∈Finset.range n,z (i+1)* ∑ j∈Finset.range (n-i-1),z
(j+1)*z (n-i-1-j))∈centeredCubeJet Z n`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `i+1=n-i` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem mem_centeredSquareJet {Z : IntervalJet} {z : ℕ → ℝ} (n : ℕ)
    (hz : ∀ i≤n,z i∈jetAt Z i) :
    (∑ i∈Finset.range n,z (i+1)*z (n-i))∈centeredSquareJet Z n := by
  -- Separate `i+1=n-i` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  apply mem_sumIntervals
  intro i hi
  by_cases h : i+1=n-i
  · rw [ite_eq_left h,← h,← pow_two]
    exact mem_squareHigh (hz (i+1) (by omega))
  · rw [ite_eq_right h]
    exact mem_roundHigh (IntervalRat.mem_mul (hz (i+1) (by omega)) (hz (n-i) (by omega)))

/--
Membership in the specified domain/enclosure: `(∑ i∈Finset.range n,z (i+1)* ∑ j∈Finset.range
(n-i-1),z (j+1)*z (n-i-1-j))∈centeredCubeJet Z n`.

Use: `chebyshev2.Numerics.mem_cubicJetStep` uses this assertion to establish the assertion
stated in that declaration.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_sumIntervals`,
`chebyshev2.Numerics.mem_roundHigh`, `chebyshev2.Numerics.mem_centeredSquareJet` with
the arguments shown in the proof.
-/
theorem mem_centeredCubeJet {Z : IntervalJet} {z : ℕ → ℝ} (n : ℕ)
    (hz : ∀ i≤n,z i∈jetAt Z i) :
    (∑ i∈Finset.range n,z (i+1)*
      ∑ j∈Finset.range (n-i-1),z (j+1)*z (n-i-1-j))∈centeredCubeJet Z n := by
  apply mem_sumIntervals
  intro i hi
  exact mem_roundHigh (IntervalRat.mem_mul (hz (i+1) (by omega))
    (mem_centeredSquareJet (n-i-1) (fun j hj => hz j (by omega))))

/--
Membership in the specified domain/enclosure: `(b (n+1)+(∑ i∈Finset.range (n+1),a (i+1)*z
(n-i))- 3*z 0*(∑ i∈Finset.range n,z (i+1)*z (n-i))- (∑ i∈Finset.range n,z (i+1)* ∑
j∈Finset.range (n-i-1),z (j+1)*z (n-i-1-j)))/(2*a 0+3*b 0/z 0) ∈cubicJetStep A B Z n`.

Use: `chebyshev2.Numerics.cubicJetCheck_encloses` uses this assertion to establish the
stated quantitative bound `JetEncloses Z (fun t => positiveCubic (a t) (b t)) s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.mem_sumIntervals`,
`chebyshev2.Numerics.mem_roundHigh`, `chebyshev2.Numerics.mem_centeredSquareJet` with
the arguments shown in the proof.
-/
theorem mem_cubicJetStep {A B Z : IntervalJet} {a b z : ℕ → ℝ} (n : ℕ)
    (ha : ∀ i≤n+1,a i∈jetAt A i) (hb : b (n+1)∈jetAt B (n+1))
    (hb0 : b 0∈jetAt B 0) (hz : ∀ i≤n,z i∈jetAt Z i)
    (hZ : 0<(jetAt Z 0).lo) (hD : 0<(cubicJetSlope A B Z).lo) :
    (b (n+1)+(∑ i∈Finset.range (n+1),a (i+1)*z (n-i))-
      3*z 0*(∑ i∈Finset.range n,z (i+1)*z (n-i))-
      (∑ i∈Finset.range n,z (i+1)*
        ∑ j∈Finset.range (n-i-1),z (j+1)*z (n-i-1-j)))/(2*a 0+3*b 0/z 0)
      ∈cubicJetStep A B Z n := by
  -- Use the identities/estimates `chebyshev2.Numerics.mem_sumIntervals`,
  -- `chebyshev2.Numerics.mem_roundHigh`, `chebyshev2.Numerics.mem_centeredSquareJet`
  -- with the arguments shown in the proof.
  have hsum := mem_sumIntervals (n+1) (fun i hi => mem_roundHigh
    (IntervalRat.mem_mul (ha (i+1) (by omega)) (hz (n-i) (by omega))))
  have hnum := mem_roundHigh (IntervalRat.mem_sub (IntervalRat.mem_sub
    (IntervalRat.mem_add hb hsum) (IntervalRat.mem_mul
      (IntervalRat.mem_mul (IntervalRat.mem_singleton 3) (hz 0 (Nat.zero_le _)))
      (mem_centeredSquareJet n hz))) (mem_centeredCubeJet n hz))
  have hslope : 2*a 0+3*b 0/z 0∈cubicJetSlope A B Z := by
    apply mem_roundHigh
    simpa only [div_eq_mul_inv,Rat.cast_ofNat] using IntervalRat.mem_add
      (IntervalRat.mem_mul (IntervalRat.mem_singleton 2) (ha 0 (by omega)))
      (IntervalRat.mem_mul (IntervalRat.mem_mul (IntervalRat.mem_singleton 3) hb0)
        (mem_inverseHigh (hz 0 (Nat.zero_le _)) hZ))
  simpa only [cubicJetStep,cubicJetNumerator,div_eq_mul_inv,Rat.cast_ofNat] using
    mem_roundHigh (IntervalRat.mem_mul hnum (mem_inverseHigh hslope hD))

/--
The stated quantitative bound `JetEncloses Z (fun t => positiveCubic (a t) (b t)) s x N`.

Use: `chebyshev2.Numerics.JetExpr.encloseCached_sound` uses this identity to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: chebyshev2, Lemma 18.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Induct on `j`; the recursive step uses the previous-stage assertion.
-/
theorem cubicJetCheck_encloses {A B Z : IntervalJet} {N : ℕ}
    (hcheck : cubicJetCheck A B Z N=true)
    {a b : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x∈s)
    (ha : ContDiffOn ℝ N a s) (hb : ContDiffOn ℝ N b s)
    (ha0 : ∀ t∈s,0≤a t) (hb0 : ∀ t∈s,0<b t)
    (hA : JetEncloses A a s x N) (hB : JetEncloses B b s x N) :
    JetEncloses Z (fun t => positiveCubic (a t) (b t)) s x N := by
  -- Induct on `j`; the recursive step uses the previous-stage assertion.
  have hc : (cubicBracketCheck (jetAt A 0) (jetAt B 0) (jetAt Z 0)=true ∧
      (0<(jetAt Z 0).lo ∧ 0<(cubicJetSlope A B Z).lo)) ∧
      (∀ n<N,intervalSubsetCheck (cubicJetStep A B Z n) (jetAt Z (n+1))=true) := by
    simpa only [cubicJetCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] using hcheck
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    cases j with
    | zero =>
      simp only [normalizedWithin_zero]
      exact cubicBracketCheck_sound hc.1.1 (by simpa using hA 0 (Nat.zero_le _))
        (by simpa using hB 0 (Nat.zero_le _))
    | succ n =>
      rw [positiveCubic_jet_recurrence hs hx (ha.of_le (by exact_mod_cast hj))
        (hb.of_le (by exact_mod_cast hj)) ha0 hb0]
      apply intervalSubsetCheck_sound (hc.2 n (by omega))
      have hmem := mem_cubicJetStep (a := fun i => normalizedWithin a s i x)
        (b := fun i => normalizedWithin b s i x)
        (z := fun i => normalizedWithin (fun t => positiveCubic (a t) (b t)) s i x) n
        (fun i hi => hA i (hi.trans hj)) (hB (n+1) hj) (hB 0 (Nat.zero_le _))
        (fun i hi => ih i (by omega) (by omega)) hc.1.2.1 hc.1.2.2
      simpa only [normalizedWithin_zero] using hmem

end chebyshev2.Numerics
