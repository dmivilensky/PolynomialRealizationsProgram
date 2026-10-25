import chebyshev2.Numerics.JetWitnessTree
import chebyshev2.Numerics.ReferenceFlowCheck
import chebyshev2.Numerics.FlowCoefficientCheck

/-!
Article: chebyshev2, Lemma 16; Appendix F.2.
`chebyshev2.Numerics.ReferenceJetSource.treeFlowSourceCheck_coefficients` instantiates
arithmetic witness trees with the actual reference amplitude and velocity.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.FlowStep.check_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics.ReferenceJetSource
open Set LeanCert.Core chebyshev2.DualCertificate
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/--
Jet witnesses for the actual rational reference quantities: profile, cubic coefficients, speed,
velocity and amplitude. Each field targets the corresponding expression tree.

Use: `chebyshev2.Numerics.ReferenceJetSource.profileTreeCheck_sound` rewrites with this
record of data and proof obligations to establish `(velocity R
W).CachedValid s x N ∧ (amplitude R W).CachedValid s x N`.

Article: chebyshev2, Lemma 16; Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
structure ReferenceProfileWitness (R : RationalReference) (W : ℕ → IntervalJet) where
  /-- Jet witness for the actual rational reference profile. -/
  p : JetWitness (p R W).body
  /-- Jet witness for the cubic linear coefficient. -/
  alpha : JetWitness (alpha R W).body
  /-- Jet witness for the cubic constant coefficient. -/
  beta : JetWitness (beta R W).body
  /-- Jet witness for the actual ground-coordinate speed. -/
  speed : JetWitness (speed R W).body
  /-- Jet witness for the actual coordinate-change velocity. -/
  velocity : JetWitness (velocity R W).body
  /-- Jet witness for the actual reference amplitude. -/
  amplitude : JetWitness (amplitude R W).body

/--
Defines `ReferenceProfileWitness.check` of type `Bool` by `K.p.check X N (W (R.count+4)) &&
K.alpha.check X N (W (R.count+5)) && K.beta.check X N (W (R.count+6)) && K.speed.check X N (W
(R.count+7)) && K.velocity.check X N (W (R.count+8)) && K.amplitude.check X N (W (R.count+9))`.

Use: `chebyshev2.Numerics.ReferenceJetSource.profileTreeCheck_sound` rewrites with this
definition to establish `(velocity R W).CachedValid s x N ∧ (amplitude
R W).CachedValid s x N`.

Article: chebyshev2, Lemma 16; Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def ReferenceProfileWitness.check {R : RationalReference} {W : ℕ → IntervalJet}
    (K : ReferenceProfileWitness R W) (X : IntervalRat) (N : ℕ) : Bool :=
  K.p.check X N (W (R.count+4)) &&
  K.alpha.check X N (W (R.count+5)) &&
  K.beta.check X N (W (R.count+6)) &&
  K.speed.check X N (W (R.count+7)) &&
  K.velocity.check X N (W (R.count+8)) &&
  K.amplitude.check X N (W (R.count+9))

/--
The precise assertion is `(velocity R W).CachedValid s x N ∧ (amplitude R W).CachedValid s x
N`.

Use: `chebyshev2.Numerics.ReferenceJetSource.treeSourceCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses JC (coefficientC R) s x N ∧ JetEncloses JA
(coefficientA R) s x N ∧ JetEncloses JB (coefficientB R sigma) s x N`.

Article: chebyshev2, Lemma 16; Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.JetExpr.CachedValid.sum`,
`chebyshev2.Numerics.JetWitness.check_sound`,
`chebyshev2.Numerics.JetExpr.Regular.body` with the arguments shown in the proof.
-/
theorem profileTreeCheck_sound {R : RationalReference} {W : ℕ → IntervalJet}
    (K : ReferenceProfileWitness R W) {X : IntervalRat} {N : ℕ}
    (hc : K.check X N=true)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hsub : s⊆Icc (0:ℝ) 1)
    {x : ℝ} (hx : x∈s) (hX : x∈X) :
    (velocity R W).CachedValid s x N ∧ (amplitude R W).CachedValid s x N := by
  -- Use the identities/estimates `chebyshev2.Numerics.JetExpr.CachedValid.sum`,
  -- `chebyshev2.Numerics.JetWitness.check_sound`,
  -- `chebyshev2.Numerics.JetExpr.Regular.body` with the arguments shown in the proof.
  simp only [ReferenceProfileWitness.check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨cp,ca⟩,cb⟩,cs⟩,cv⟩,cm⟩ := hc
  have vp : (p R W).body.CachedValid s x N := by
    change True ∧ (JetExpr.sum (List.ofFn (term R W))).CachedValid s x N
    refine ⟨trivial,JetExpr.CachedValid.sum ?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    simp only [term,Q,h,JetExpr.scale,JetExpr.cube,JetExpr.CachedValid]
    trivial
  have hp := JetWitness.check_sound K.p hs hx hX ((p_regular R W).mono hsub).body vp cp
  have va : (alpha R W).body.CachedValid s x N := by
    simp only [alpha,inverseK,k,h,JetExpr.body,JetExpr.scale,JetExpr.cube,JetExpr.CachedValid]
    trivial
  have ha := JetWitness.check_sound K.alpha hs hx hX
    ((root_regular R W).1.1.mono hsub).body va ca
  have vb : (beta R W).body.CachedValid s x N := by
    change True ∧ ((JetEncloses (W (R.count+4)) (p R W).body.value s x N ∧
      h.CachedValid s x N) ∧ (inverseK R W).CachedValid s x N)
    exact ⟨trivial,⟨⟨hp,by trivial⟩,by trivial⟩⟩
  have hb := JetWitness.check_sound K.beta hs hx hX
    ((root_regular R W).1.2.mono hsub).body vb cb
  have vs : (speed R W).body.CachedValid s x N := by
    change (True ∧ (True ∧ h.CachedValid s x N)) ∧
      (True ∧ ((JetEncloses (W (R.count+4)) (p R W).body.value s x N ∧
        h.CachedValid s x N) ∧
        (JetEncloses (W (R.count+5)) (alpha R W).body.value s x N ∧
         JetEncloses (W (R.count+6)) (beta R W).body.value s x N)))
    exact ⟨⟨trivial,⟨trivial,by trivial⟩⟩,⟨trivial,⟨⟨hp,by trivial⟩,ha,hb⟩⟩⟩
  have hspeed := JetWitness.check_sound K.speed hs hx hX
    ((speed_regular R W).mono hsub).body vs cs
  have vv : (velocity R W).body.CachedValid s x N := ⟨trivial,hspeed⟩
  have hv := JetWitness.check_sound K.velocity hs hx hX
    ((velocity_regular R W).mono hsub).body vv cv
  have vm : (amplitude R W).body.CachedValid s x N := ⟨trivial,ha,hb⟩
  have rm : (amplitude R W).Regular s := ⟨trivial,(root_regular R W).mono hsub⟩
  have hm := JetWitness.check_sound K.amplitude hs hx hX rm.body vm cm
  exact ⟨hv,hm⟩

/--
Defines `treeSourceCheck` of type `Bool` by `K.check X N && (C R W).checkCachedInto X N JC &&
(A R W).checkCachedInto X N JA && (B R W sigma).checkCachedInto X N JB`.

Use: `chebyshev2.Numerics.ReferenceJetSource.treeFlowSourceCheck` uses this definition in
the displayed construction of `treeFlowSourceCheck`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Lemma 16; Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def treeSourceCheck (R : RationalReference) (sigma : ℚ) (W : ℕ → IntervalJet)
    (K : ReferenceProfileWitness R W) (X : IntervalRat) (N : ℕ) (JC JA JB : IntervalJet) : Bool :=
  K.check X N && (C R W).checkCachedInto X N JC &&
    (A R W).checkCachedInto X N JA && (B R W sigma).checkCachedInto X N JB

/--
The precise assertion is `JetEncloses JC (coefficientC R) s x N ∧ JetEncloses JA (coefficientA
R) s x N ∧ JetEncloses JB (coefficientB R sigma) s x N`.

Use: `chebyshev2.Numerics.ReferenceJetSource.treeFlowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (coefficientC R) (coefficientA
R) (coefficientB R sigma) a`.

Article: chebyshev2, Lemma 16; Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates
`chebyshev2.Numerics.ReferenceJetSource.profileTreeCheck_sound`,
`chebyshev2.Numerics.JetExpr.checkCachedInto_sound`,
`chebyshev2.Numerics.JetExpr.Regular.mono` with the arguments shown in the proof.
-/
theorem treeSourceCheck_sound {R : RationalReference} {sigma : ℚ} {W : ℕ → IntervalJet}
    {K : ReferenceProfileWitness R W} {X : IntervalRat} {N : ℕ} {JC JA JB : IntervalJet}
    (hc : treeSourceCheck R sigma W K X N JC JA JB=true)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hsub : s⊆Icc (0:ℝ) 1)
    {x : ℝ} (hx : x∈s) (hX : x∈X) :
    JetEncloses JC (coefficientC R) s x N ∧
      JetEncloses JA (coefficientA R) s x N ∧ JetEncloses JB (coefficientB R sigma) s x N := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.ReferenceJetSource.profileTreeCheck_sound`,
  -- `chebyshev2.Numerics.JetExpr.checkCachedInto_sound`,
  -- `chebyshev2.Numerics.JetExpr.Regular.mono` with the arguments shown in the proof.
  simp only [treeSourceCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp,cC⟩,cA⟩,cB⟩ := hc
  obtain ⟨hv,hm⟩ := profileTreeCheck_sound K hp hs hsub hx hX
  have hC := JetExpr.checkCachedInto_sound hs hx hX ((C_regular R W).mono hsub)
    ⟨⟨hv,by trivial⟩,hm⟩ cC
  have hA := JetExpr.checkCachedInto_sound hs hx hX ((A_regular R W).mono hsub) ⟨trivial,hv⟩ cA
  have hB := JetExpr.checkCachedInto_sound hs hx hX ((B_regular R W sigma).mono hsub) ⟨trivial,hv⟩ cB
  exact ⟨fun j hj => by
      rw [←normalizedWithin_congr ((C_value R W).mono hsub) j hx];exact hC j hj,
    fun j hj => by
      rw [←normalizedWithin_congr ((A_value R W).mono hsub) j hx];exact hA j hj,
    fun j hj => by
      rw [←normalizedWithin_congr ((B_value R W sigma).mono hsub) j hx];exact hB j hj⟩

/--
Defines `treeFlowSourceCheck` of type `Bool` by `flowCoefficientCheck (treeSourceCheck R sigma
P KP) (treeSourceCheck R sigma H KH) a W`.

Use: `chebyshev2.Numerics.ReferenceJetSource.treeFlowSourceCheck_coefficients` uses this
definition to establish `W.Coefficients (coefficientC R) (coefficientA
R) (coefficientB R sigma) a`.

Article: chebyshev2, Lemma 16; Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
def treeFlowSourceCheck (R : RationalReference) (sigma a : ℚ) (P H : ℕ → IntervalJet)
    (KP : ReferenceProfileWitness R P) (KH : ReferenceProfileWitness R H) (W : FlowStep) : Bool :=
  flowCoefficientCheck (treeSourceCheck R sigma P KP) (treeSourceCheck R sigma H KH) a W

/--
The precise assertion is `W.Coefficients (coefficientC R) (coefficientA R) (coefficientB R
sigma) a`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16; Appendix F.2.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.flowCoefficientCheck_sound`,
`chebyshev2.Numerics.ReferenceJetSource.treeSourceCheck_sound`,
`chebyshev2.Numerics.ReferenceJetSource.coefficientC_smooth` with the arguments shown in
the proof.
-/
theorem treeFlowSourceCheck_coefficients {R : RationalReference} {sigma a : ℚ}
    {P H : ℕ → IntervalJet} {KP : ReferenceProfileWitness R P} {KH : ReferenceProfileWitness R H}
    {W : FlowStep} (hcheck : treeFlowSourceCheck R sigma a P H KP KH W=true) :
    W.Coefficients (coefficientC R) (coefficientA R) (coefficientB R sigma) a := by
  -- Use the identities/estimates `chebyshev2.Numerics.flowCoefficientCheck_sound`,
  -- `chebyshev2.Numerics.ReferenceJetSource.treeSourceCheck_sound`,
  -- `chebyshev2.Numerics.ReferenceJetSource.coefficientC_smooth` with the arguments shown
  -- in the proof.
  apply flowCoefficientCheck_sound _ _ _ _ hcheck
  · intro Q hQ X N JC JA JB hc s hs hsub x hx hX
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    have hsub' : s⊆Icc (0:ℝ) 1 := by simpa only [Rat.cast_zero,Rat.cast_one] using hsub
    rcases hQ with rfl | rfl <;> exact treeSourceCheck_sound hc hs hsub' hx hX
  · simpa only [Rat.cast_zero,Rat.cast_one] using coefficientC_smooth R
  · simpa only [Rat.cast_zero,Rat.cast_one] using coefficientA_smooth R
  · simpa only [Rat.cast_zero,Rat.cast_one] using coefficientB_smooth R sigma

end chebyshev2.Numerics.ReferenceJetSource
