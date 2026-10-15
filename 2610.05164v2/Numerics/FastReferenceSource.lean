import «2610.05164v2».Numerics.CachedJetExpr

/-!
Article: 2610.05164v2, Lemma 16; Appendix F.2.
`«2610.05164v2».Numerics.ReferenceJetSource.graphCheck_sound` provides checked actual reference
coefficient jets through shared expression graphs.
Interface: its result can discharge the corresponding enclosure premises of
`«2610.05164v2».Numerics.FlowStep.check_sound`.
Proof chain: 2610.05164v2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace «2610.05164v2».Numerics.ReferenceJetSource
open Set LeanCert.Core «2610.05164v2».DualCertificate
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/--
Defines `profileCheck` of type `Bool`. The displayed construction fixes its component data; its
proof fields enforce the listed compatibility properties.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.graphCheck` uses this definition in the
displayed construction of `graphCheck`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 16; Appendix F.2.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def profileCheck (R : RationalReference) (W : ℕ → IntervalJet)
    (X : IntervalRat) (N : ℕ) : Bool :=
  (p R W).body.checkCachedInto X N (W (R.count+4)) &&
  (alpha R W).body.checkCachedInto X N (W (R.count+5)) &&
  (beta R W).body.checkCachedInto X N (W (R.count+6)) &&
  (speed R W).body.checkCachedInto X N (W (R.count+7)) &&
  (velocity R W).body.checkCachedInto X N (W (R.count+8)) &&
  (amplitude R W).body.checkCachedInto X N (W (R.count+9))

/--
The precise assertion is `(velocity R W).CachedValid s x N ∧ (amplitude R W).CachedValid s x
N`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.graphCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses JC (C R W).value s x N ∧ JetEncloses JA (A R
W).value s x N ∧ JetEncloses JB (B R W sigma).value s x N`.

Article: 2610.05164v2, Lemma 16; Appendix F.2.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.CachedValid.sum`,
`«2610.05164v2».Numerics.JetExpr.checkCachedInto_sound`,
`«2610.05164v2».Numerics.JetExpr.Regular.body` with the arguments shown in the proof.
-/
theorem profileCheck_sound {R : RationalReference} {W : ℕ → IntervalJet}
    {X : IntervalRat} {N : ℕ}
    (hc : profileCheck R W X N=true)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hsub : s⊆Icc (0:ℝ) 1)
    {x : ℝ} (hx : x∈s) (hX : x∈X) :
    (velocity R W).CachedValid s x N ∧ (amplitude R W).CachedValid s x N := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.CachedValid.sum`,
  -- `«2610.05164v2».Numerics.JetExpr.checkCachedInto_sound`,
  -- `«2610.05164v2».Numerics.JetExpr.Regular.body` with the arguments shown in the proof.
  simp only [profileCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨cp,ca⟩,cb⟩,cs⟩,cv⟩,cm⟩ := hc
  have vp : (p R W).body.CachedValid s x N := by
    change True ∧ (JetExpr.sum (List.ofFn (term R W))).CachedValid s x N
    refine ⟨trivial,JetExpr.CachedValid.sum ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    simp only [term,Q,h,JetExpr.scale,JetExpr.cube,JetExpr.CachedValid]
    trivial
  have hp := JetExpr.checkCachedInto_sound hs hx hX ((p_regular R W).mono hsub).body vp cp
  have va : (alpha R W).body.CachedValid s x N := by
    simp only [alpha,inverseK,k,h,JetExpr.body,JetExpr.scale,JetExpr.cube,JetExpr.CachedValid]
    trivial
  have ha := JetExpr.checkCachedInto_sound hs hx hX
    ((root_regular R W).1.1.mono hsub).body va ca
  have vb : (beta R W).body.CachedValid s x N := by
    change True ∧ ((JetEncloses (W (R.count+4)) (p R W).body.value s x N ∧
      h.CachedValid s x N) ∧ (inverseK R W).CachedValid s x N)
    exact ⟨trivial,⟨⟨hp,by trivial⟩,by trivial⟩⟩
  have hb := JetExpr.checkCachedInto_sound hs hx hX
    ((root_regular R W).1.2.mono hsub).body vb cb
  have vs : (speed R W).body.CachedValid s x N := by
    change (True ∧ (True ∧ h.CachedValid s x N)) ∧
      (True ∧ ((JetEncloses (W (R.count+4)) (p R W).body.value s x N ∧
        h.CachedValid s x N) ∧
        (JetEncloses (W (R.count+5)) (alpha R W).body.value s x N ∧
         JetEncloses (W (R.count+6)) (beta R W).body.value s x N)))
    exact ⟨⟨trivial,⟨trivial,by trivial⟩⟩,⟨trivial,⟨⟨hp,by trivial⟩,ha,hb⟩⟩⟩
  have hspeed := JetExpr.checkCachedInto_sound hs hx hX
    ((speed_regular R W).mono hsub).body vs cs
  have vv : (velocity R W).body.CachedValid s x N := ⟨trivial,hspeed⟩
  have hv := JetExpr.checkCachedInto_sound hs hx hX
    ((velocity_regular R W).mono hsub).body vv cv
  have vm : (amplitude R W).body.CachedValid s x N := ⟨trivial,ha,hb⟩
  have rm : (amplitude R W).Regular s := ⟨trivial,(root_regular R W).mono hsub⟩
  have hm := JetExpr.checkCachedInto_sound hs hx hX rm.body vm cm
  exact ⟨hv,hm⟩

/--
Defines `graphCheck` of type `Bool` by `profileCheck R W X N && (C R W).checkCachedInto X N JC
&& (A R W).checkCachedInto X N JA && (B R W sigma).checkCachedInto X N JB`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.graphCheck_sound` rewrites with this
definition to establish `JetEncloses JC (C R W).value s x N ∧
JetEncloses JA (A R W).value s x N ∧ JetEncloses JB (B R W sigma).value s x N`.

Article: 2610.05164v2, Lemma 16; Appendix F.2.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def graphCheck (R : RationalReference) (sigma : ℚ) (W : ℕ → IntervalJet)
    (X : IntervalRat) (N : ℕ) (JC JA JB : IntervalJet) : Bool :=
  profileCheck R W X N && (C R W).checkCachedInto X N JC &&
    (A R W).checkCachedInto X N JA && (B R W sigma).checkCachedInto X N JB

/--
The precise assertion is `JetEncloses JC (C R W).value s x N ∧ JetEncloses JA (A R W).value s x
N ∧ JetEncloses JB (B R W sigma).value s x N`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.sourceCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses JC (coefficientC R) s x N ∧ JetEncloses JA
(coefficientA R) s x N ∧ JetEncloses JB (coefficientB R sigma) s x N`.

Article: 2610.05164v2, Lemma 16; Appendix F.2.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.profileCheck_sound`,
`«2610.05164v2».Numerics.JetExpr.checkCachedInto_sound`,
`«2610.05164v2».Numerics.JetExpr.Regular.mono` with the arguments shown in the proof.
-/
theorem graphCheck_sound {R : RationalReference} {sigma : ℚ} {W : ℕ → IntervalJet}
    {X : IntervalRat} {N : ℕ} {JC JA JB : IntervalJet}
    (hc : graphCheck R sigma W X N JC JA JB=true)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hsub : s⊆Icc (0:ℝ) 1)
    {x : ℝ} (hx : x∈s) (hX : x∈X) :
    JetEncloses JC (C R W).value s x N ∧
      JetEncloses JA (A R W).value s x N ∧ JetEncloses JB (B R W sigma).value s x N := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.ReferenceJetSource.profileCheck_sound`,
  -- `«2610.05164v2».Numerics.JetExpr.checkCachedInto_sound`,
  -- `«2610.05164v2».Numerics.JetExpr.Regular.mono` with the arguments shown in the proof.
  simp only [graphCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp,cC⟩,cA⟩,cB⟩ := hc
  obtain ⟨hv,hm⟩ := profileCheck_sound hp hs hsub hx hX
  exact ⟨JetExpr.checkCachedInto_sound hs hx hX ((C_regular R W).mono hsub)
      ⟨⟨hv,by trivial⟩,hm⟩ cC,
    JetExpr.checkCachedInto_sound hs hx hX ((A_regular R W).mono hsub) ⟨trivial,hv⟩ cA,
    JetExpr.checkCachedInto_sound hs hx hX ((B_regular R W sigma).mono hsub) ⟨trivial,hv⟩ cB⟩

end «2610.05164v2».Numerics.ReferenceJetSource
