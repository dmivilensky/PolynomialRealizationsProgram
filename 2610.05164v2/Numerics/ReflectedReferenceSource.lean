import «2610.05164v2».Numerics.TreeReferenceSource
import «2610.05164v2».Numerics.JetReflection

/-!
Article: 2610.05164v2, Section 4.1.
The right reference chart uses v = 2-t.
Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFilter_ode` feeds
`«2610.05164v2».Numerics.ReferenceJetSource.actual_right_filter_step` (actual right filter step).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics.ReferenceJetSource
open Set LeanCert.Core «2610.05164v2».DualCertificate
open scoped Pointwise ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/--
Defines `reflectedInterval` of type `IntervalRat` by `⟨2-X.hi,2-X.lo,by linarith [X.le]⟩`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.mem_reflectedInterval` rewrites with this
definition to establish membership in the specified domain/enclosure: `2-x∈reflectedInterval
X`.

Article: 2610.05164v2, Section 4.1.
-/
def reflectedInterval (X : IntervalRat) : IntervalRat := ⟨2-X.hi,2-X.lo,by linarith [X.le]⟩

/--
Membership in the specified domain/enclosure: `2-x∈reflectedInterval X`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightSourceCheck_sound` uses this assertion to
establish the precise assertion is `JetEncloses JC (rightCoefficientC R) s x N ∧ JetEncloses JA
(rightCoefficientA R) s x N ∧ JetEncloses JB (rightCoefficientB R sigma) s x N`.

Article: 2610.05164v2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mem_reflectedInterval {X : IntervalRat} {x : ℝ} (hx : x∈X) :
    2-x∈reflectedInterval X := by
  simp only [IntervalRat.mem_def,reflectedInterval,Rat.cast_sub,Rat.cast_ofNat]
  constructor <;> linarith [hx.1,hx.2]

/--
Defines `rightCoefficientC` of type `ℝ` by `coefficientC R (2-v)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFilter_ode` uses this definition to
establish the derivative within the stated domain: `HasDerivWithinAt (rightFilter R hsigma)
(rightCoefficientC R v+rightCoefficientA R v*rightFilter R hsigma v+ rightCoefficientB R sigma
v*(rightFilter R hsigma v)^2) (Icc (1:ℝ) 2) v`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def rightCoefficientC (R : RationalReference) (v : ℝ) : ℝ := coefficientC R (2-v)
/--
Defines `rightCoefficientA` of type `ℝ` by `coefficientA R (2-v)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFilter_ode` uses this definition to
establish the derivative within the stated domain: `HasDerivWithinAt (rightFilter R hsigma)
(rightCoefficientC R v+rightCoefficientA R v*rightFilter R hsigma v+ rightCoefficientB R sigma
v*(rightFilter R hsigma v)^2) (Icc (1:ℝ) 2) v`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def rightCoefficientA (R : RationalReference) (v : ℝ) : ℝ := coefficientA R (2-v)
/--
Defines `rightCoefficientB` of type `ℝ` by `coefficientB R sigma (2-v)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFilter_ode` uses this definition to
establish the derivative within the stated domain: `HasDerivWithinAt (rightFilter R hsigma)
(rightCoefficientC R v+rightCoefficientA R v*rightFilter R hsigma v+ rightCoefficientB R sigma
v*(rightFilter R hsigma v)^2) (Icc (1:ℝ) 2) v`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def rightCoefficientB (R : RationalReference) (sigma : ℚ) (v : ℝ) : ℝ :=
  coefficientB R sigma (2-v)

/--
Defines `rightSourceCheck` of type `Bool` by `treeSourceCheck R sigma W K (reflectedInterval X)
N TC TA TB && jetSubsetCheck (reflectJet TC N) JC N && jetSubsetCheck (reflectJet TA N) JA N &&
jetSubsetCheck (reflectJet TB N) JB N`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFlowSourceCheck` uses this definition in
the displayed construction of `rightFlowSourceCheck`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def rightSourceCheck (R : RationalReference) (sigma : ℚ) (W : ℕ → IntervalJet)
    (K : ReferenceProfileWitness R W) (TC TA TB : IntervalJet)
    (X : IntervalRat) (N : ℕ) (JC JA JB : IntervalJet) : Bool :=
  treeSourceCheck R sigma W K (reflectedInterval X) N TC TA TB &&
    jetSubsetCheck (reflectJet TC N) JC N && jetSubsetCheck (reflectJet TA N) JA N &&
    jetSubsetCheck (reflectJet TB N) JB N

/--
The precise assertion is `JetEncloses JC (rightCoefficientC R) s x N ∧ JetEncloses JA
(rightCoefficientA R) s x N ∧ JetEncloses JB (rightCoefficientB R sigma) s x N`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFlowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (rightCoefficientC R)
(rightCoefficientA R) (rightCoefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.reflectSet_eq_image`,
`«2610.05164v2».Numerics.ReferenceJetSource.treeSourceCheck_sound`,
`«2610.05164v2».Numerics.uniqueDiffOn_reflect` with the arguments shown in the proof.
-/
theorem rightSourceCheck_sound {R : RationalReference} {sigma : ℚ} {W : ℕ → IntervalJet}
    {K : ReferenceProfileWitness R W} {TC TA TB JC JA JB : IntervalJet}
    {X : IntervalRat} {N : ℕ} (hc : rightSourceCheck R sigma W K TC TA TB X N JC JA JB=true)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hsub : s⊆Icc (1:ℝ) 2)
    {x : ℝ} (hx : x∈s) (hX : x∈X) :
    JetEncloses JC (rightCoefficientC R) s x N ∧
      JetEncloses JA (rightCoefficientA R) s x N ∧ JetEncloses JB (rightCoefficientB R sigma) s x N := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.reflectSet_eq_image`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.treeSourceCheck_sound`,
  -- `«2610.05164v2».Numerics.uniqueDiffOn_reflect` with the arguments shown in the proof.
  simp only [rightSourceCheck,Bool.and_eq_true] at hc
  have hsub' : (2:ℝ)+ᵥ -s⊆Icc (0:ℝ) 1 := by
    rw [reflectSet_eq_image]
    rintro y ⟨v,hv,rfl⟩
    have h := hsub hv
    constructor <;> linarith [h.1,h.2]
  have hx' : (2:ℝ)-x∈(2:ℝ)+ᵥ -s := by
    rw [reflectSet_eq_image]
    exact ⟨x,hx,rfl⟩
  have h := treeSourceCheck_sound hc.1.1.1 (uniqueDiffOn_reflect hs 2) hsub' hx'
    (mem_reflectedInterval hX)
  exact ⟨jetSubsetCheck_sound hc.1.1.2 (reflectJet_encloses h.1),
    jetSubsetCheck_sound hc.1.2 (reflectJet_encloses h.2.1),
    jetSubsetCheck_sound hc.2 (reflectJet_encloses h.2.2)⟩

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (rightCoefficientC R) (Icc (1:ℝ) 2)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFlowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (rightCoefficientC R)
(rightCoefficientA R) (rightCoefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.coefficientC_smooth` with the arguments shown in
the proof.
-/
theorem rightCoefficientC_smooth (R : RationalReference) :
    ContDiffOn ℝ ∞ (rightCoefficientC R) (Icc (1:ℝ) 2) := by
  apply (coefficientC_smooth R).comp (contDiffOn_const.sub contDiffOn_id)
  intro x hx
  change 0≤2-x ∧ 2-x≤1
  constructor <;> linarith [hx.1,hx.2]

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (rightCoefficientA R) (Icc (1:ℝ) 2)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFlowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (rightCoefficientC R)
(rightCoefficientA R) (rightCoefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.coefficientA_smooth` with the arguments shown in
the proof.
-/
theorem rightCoefficientA_smooth (R : RationalReference) :
    ContDiffOn ℝ ∞ (rightCoefficientA R) (Icc (1:ℝ) 2) := by
  apply (coefficientA_smooth R).comp (contDiffOn_const.sub contDiffOn_id)
  intro x hx
  change 0≤2-x ∧ 2-x≤1
  constructor <;> linarith [hx.1,hx.2]

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (rightCoefficientB R sigma) (Icc (1:ℝ) 2)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFlowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (rightCoefficientC R)
(rightCoefficientA R) (rightCoefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.coefficientB_smooth` with the arguments shown in
the proof.
-/
theorem rightCoefficientB_smooth (R : RationalReference) (sigma : ℚ) :
    ContDiffOn ℝ ∞ (rightCoefficientB R sigma) (Icc (1:ℝ) 2) := by
  apply (coefficientB_smooth R sigma).comp (contDiffOn_const.sub contDiffOn_id)
  intro x hx
  change 0≤2-x ∧ 2-x≤1
  constructor <;> linarith [hx.1,hx.2]

/--
Defines `rightFilter` of type `ℝ` by `(referenceData R).normalizedReflectedFilter (σ :=
(sigma:ℝ)) (by exact_mod_cast hsigma) (2-v)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.rightFilter_ode` uses this definition to
establish the derivative within the stated domain: `HasDerivWithinAt (rightFilter R hsigma)
(rightCoefficientC R v+rightCoefficientA R v*rightFilter R hsigma v+ rightCoefficientB R sigma
v*(rightFilter R hsigma v)^2) (Icc (1:ℝ) 2) v`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def rightFilter (R : RationalReference) {sigma : ℚ} (hsigma : 0<sigma) (v : ℝ) : ℝ :=
  (referenceData R).normalizedReflectedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) (2-v)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (rightFilter R hsigma) (Icc (1:ℝ) 2)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_right_filter_step` uses this assertion
to establish membership in the specified domain/enclosure: `rightFilter R hsigma
((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedReflectedFilter_smooth` with the arguments
shown in the proof.
-/
theorem rightFilter_smooth (R : RationalReference) {sigma : ℚ} (hsigma : 0<sigma) :
    ContDiffOn ℝ ∞ (rightFilter R hsigma) (Icc (1:ℝ) 2) := by
  apply ((referenceData R).normalizedReflectedFilter_smooth (σ := (sigma:ℝ))
    (by exact_mod_cast hsigma)).comp (contDiffOn_const.sub contDiffOn_id)
  intro x hx
  change 0≤2-x ∧ 2-x≤1
  constructor <;> linarith [hx.1,hx.2]

/--
Exact identity `rightFilter R hsigma 1=(referenceData R).normalizedFilter (σ := (sigma:ℝ)) (by
exact_mod_cast hsigma) 1`.

Use: `«2610.05164v2».Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` uses
this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.X_one` with the
arguments shown in the proof.
-/
theorem rightFilter_one (R : RationalReference) {sigma : ℚ} (hsigma : 0<sigma) :
    rightFilter R hsigma 1=(referenceData R).normalizedFilter (σ := (sigma:ℝ))
      (by exact_mod_cast hsigma) 1 := by
  simp only [rightFilter,«2610.05164v2».Calibration.ReferenceData.normalizedReflectedFilter,
    «2610.05164v2».Calibration.ReferenceData.normalizedFilter,«2610.05164v2».Calibration.ReferenceData.normalizedX,
    one_pow,show (2:ℝ)-1=1 by norm_num,(referenceData R).X_one,neg_zero]

/--
The derivative within the stated domain: `HasDerivWithinAt (rightFilter R hsigma)
(rightCoefficientC R v+rightCoefficientA R v*rightFilter R hsigma v+ rightCoefficientB R sigma
v*(rightFilter R hsigma v)^2) (Icc (1:ℝ) 2) v`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_right_filter_step` uses this derivative
formula to establish membership in the specified domain/enclosure: `rightFilter R hsigma
((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedReflectedFilter_derivative` with the
arguments shown in the proof.
-/
theorem rightFilter_ode (R : RationalReference) {sigma : ℚ} (hsigma : 0<sigma)
    {v : ℝ} (hv : v∈Icc (1:ℝ) 2) :
    HasDerivWithinAt (rightFilter R hsigma)
      (rightCoefficientC R v+rightCoefficientA R v*rightFilter R hsigma v+
        rightCoefficientB R sigma v*(rightFilter R hsigma v)^2) (Icc (1:ℝ) 2) v := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedReflectedFilter_derivative` with the
  -- arguments shown in the proof.
  have ht : 2-v∈Icc (0:ℝ) 1 := by constructor <;> linarith [hv.1,hv.2]
  have h := ((referenceData R).normalizedReflectedFilter_derivative (σ := (sigma:ℝ))
    (by exact_mod_cast hsigma) ht).comp v
    ((hasDerivWithinAt_id v (Icc (1:ℝ) 2)).const_sub 2) (by
      intro x hx
      constructor <;> linarith [hx.1,hx.2])
  convert! h using 1
  dsimp only [rightCoefficientC,rightCoefficientA,rightCoefficientB,
    coefficientC,coefficientA,coefficientB,rightFilter]
  ring

/--
Defines `rightFlowSourceCheck` of type `Bool` by `flowCoefficientCheck (rightSourceCheck R
sigma P KP PT.1 PT.2.1 PT.2.2) (rightSourceCheck R sigma H KH HT.1 HT.2.1 HT.2.2) a W 1 2`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_right_filter_step` uses this definition
to establish membership in the specified domain/enclosure: `rightFilter R hsigma
((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.
-/
def rightFlowSourceCheck (R : RationalReference) (sigma a : ℚ) (P H : ℕ → IntervalJet)
    (KP : ReferenceProfileWitness R P) (KH : ReferenceProfileWitness R H)
    (PT HT : IntervalJet × IntervalJet × IntervalJet) (W : FlowStep) : Bool :=
  flowCoefficientCheck (rightSourceCheck R sigma P KP PT.1 PT.2.1 PT.2.2)
    (rightSourceCheck R sigma H KH HT.1 HT.2.1 HT.2.2) a W 1 2

/--
The precise assertion is `W.Coefficients (rightCoefficientC R) (rightCoefficientA R)
(rightCoefficientB R sigma) a`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_right_filter_step` uses this assertion
to establish membership in the specified domain/enclosure: `rightFilter R hsigma
((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.flowCoefficientCheck_sound`,
`«2610.05164v2».Numerics.ReferenceJetSource.rightSourceCheck_sound`,
`«2610.05164v2».Numerics.ReferenceJetSource.rightCoefficientC_smooth` with the arguments shown
in the proof.
-/
theorem rightFlowSourceCheck_coefficients {R : RationalReference} {sigma a : ℚ}
    {P H : ℕ → IntervalJet} {KP : ReferenceProfileWitness R P} {KH : ReferenceProfileWitness R H}
    {PT HT : IntervalJet × IntervalJet × IntervalJet} {W : FlowStep}
    (hcheck : rightFlowSourceCheck R sigma a P H KP KH PT HT W=true) :
    W.Coefficients (rightCoefficientC R) (rightCoefficientA R) (rightCoefficientB R sigma) a := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.flowCoefficientCheck_sound`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.rightSourceCheck_sound`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.rightCoefficientC_smooth` with the arguments
  -- shown in the proof.
  apply flowCoefficientCheck_sound _ _ _ _ hcheck
  · intro Q hQ X N JC JA JB hc s hs hsub x hx hX
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    have hsub' : s⊆Icc (1:ℝ) 2 := by simpa only [Rat.cast_one,Rat.cast_ofNat] using hsub
    rcases hQ with rfl | rfl <;> exact rightSourceCheck_sound hc hs hsub' hx hX
  · simpa only [Rat.cast_one,Rat.cast_ofNat] using rightCoefficientC_smooth R
  · simpa only [Rat.cast_one,Rat.cast_ofNat] using rightCoefficientA_smooth R
  · simpa only [Rat.cast_one,Rat.cast_ofNat] using rightCoefficientB_smooth R sigma

/--
Membership in the specified domain/enclosure: `rightFilter R hsigma ((a:ℝ)+W.width)∈W.output`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.rightFlowSourceCheck_coefficients`,
`«2610.05164v2».Numerics.flowCoefficientCheck_domain`,
`«2610.05164v2».Numerics.FlowStep.check_sound` with the arguments shown in the proof.
-/
theorem actual_right_filter_step {R : RationalReference} {sigma a : ℚ} (hsigma : 0<sigma)
    {P H : ℕ → IntervalJet} {KP : ReferenceProfileWitness R P} {KH : ReferenceProfileWitness R H}
    {PT HT : IntervalJet × IntervalJet × IntervalJet} {W : FlowStep}
    (hsource : rightFlowSourceCheck R sigma a P H KP KH PT HT W=true) (hcheck : W.check=true)
    (hinitial : rightFilter R hsigma a∈W.initial) :
    rightFilter R hsigma ((a:ℝ)+W.width)∈W.output := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.ReferenceJetSource.rightFlowSourceCheck_coefficients`,
  -- `«2610.05164v2».Numerics.flowCoefficientCheck_domain`,
  -- `«2610.05164v2».Numerics.FlowStep.check_sound` with the arguments shown in the proof.
  have hc := rightFlowSourceCheck_coefficients hsource
  obtain ⟨hh,ha,hb⟩ := flowCoefficientCheck_domain hsource
  have har : (1:ℝ)≤a := by exact_mod_cast ha
  have hbr : (a:ℝ)+W.width≤2 := by exact_mod_cast hb
  have hsub : Icc (a:ℝ) (a+W.width)⊆Icc (1:ℝ) 2 := Icc_subset_Icc har hbr
  apply W.check_sound hcheck hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
    ((rightFilter_smooth R hsigma).continuousOn.mono hsub) _ hinitial
  intro t ht
  exact (rightFilter_ode R hsigma (hsub ⟨ht.1.le,ht.2.le⟩)).hasDerivAt
    (Icc_mem_nhds (lt_of_le_of_lt har ht.1) (ht.2.trans_le hbr))

end «2610.05164v2».Numerics.ReferenceJetSource
