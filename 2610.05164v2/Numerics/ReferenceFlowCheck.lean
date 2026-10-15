import «2610.05164v2».Numerics.FastReferenceSource
import «2610.05164v2».Numerics.FlowChain

/-!
Article: 2610.05164v2, Section 4.1.
Reference flow acceptance with coefficient premises discharged by the literal source evaluator.
Use: `«2610.05164v2».Numerics.ReferenceJetSource.coefficientB` feeds
`«2610.05164v2».Numerics.ReferenceJetSource.flowSourceCheck_coefficients` (flow Source Check
coefficients).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics
open Set LeanCert.Core «2610.05164v2».DualCertificate
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/--
Defines `JetExpr.checkInto` of type `Bool` by `match e.enclose X N with | none => false | some
K => jetSubsetCheck K J N`.

Use: `«2610.05164v2».Numerics.JetExpr.checkInto_sound` uses this definition to establish the
precise assertion is `JetEncloses J e.value s x N`.

Article: 2610.05164v2, Section 4.1.
-/
def JetExpr.checkInto (e : JetExpr) (X : IntervalRat) (N : ℕ) (J : IntervalJet) : Bool :=
  match e.enclose X N with
  | none => false
  | some K => jetSubsetCheck K J N

/--
The precise assertion is `JetEncloses J e.value s x N`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.jetSubsetCheck_sound`,
`«2610.05164v2».Numerics.JetExpr.enclose_sound` with the arguments shown in the proof.
-/
theorem JetExpr.checkInto_sound {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {x : ℝ} (hx : x∈s) {X : IntervalRat} (hX : x∈X) {N : ℕ} {e : JetExpr}
    (hr : e.Regular s) {J : IntervalJet} (h : e.checkInto X N J=true) :
    JetEncloses J e.value s x N := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.jetSubsetCheck_sound`,
  -- `«2610.05164v2».Numerics.JetExpr.enclose_sound` with the arguments shown in the proof.
  cases he : e.enclose X N with
  | none => simp [checkInto,he] at h
  | some K =>
    exact jetSubsetCheck_sound (by simpa only [checkInto,he] using h)
      (e.enclose_sound hs hx hX N hr he)

namespace ReferenceJetSource
variable (R : RationalReference)

/--
Defines `coefficientC` of type `ℝ` by `(referenceData R).normalizedVelocity t*(referenceData
R).k* (t*(referenceData R).normalizedRoot t)^2`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.C_value` rewrites with this definition to
establish pointwise equality on the specified domain: `EqOn (C R W).value (coefficientC R) (Icc
(0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def coefficientC (t : ℝ) : ℝ :=
  (referenceData R).normalizedVelocity t*(referenceData R).k*
    (t*(referenceData R).normalizedRoot t)^2
/--
Defines `coefficientA` of type `ℝ` by `-2*(referenceData R).normalizedVelocity t`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.A_value` rewrites with this definition to
establish pointwise equality on the specified domain: `EqOn (A R W).value (coefficientA R) (Icc
(0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def coefficientA (t : ℝ) : ℝ := -2*(referenceData R).normalizedVelocity t
/--
Defines `coefficientB` of type `ℝ` by `-(sigma:ℝ)*(referenceData R).normalizedVelocity t`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.B_value` rewrites with this definition to
establish pointwise equality on the specified domain: `EqOn (B R W sigma).value (coefficientB R
sigma) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def coefficientB (sigma : ℚ) (t : ℝ) : ℝ :=
  -(sigma:ℝ)*(referenceData R).normalizedVelocity t

/--
Pointwise equality on the specified domain: `EqOn (C R W).value (coefficientC R) (Icc (0:ℝ)
1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_filter_step` rewrites with this
pointwise identity to establish membership in the specified domain/enclosure: `(referenceData
R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.velocity_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.k_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.root_value` with the arguments shown in the proof.
-/
theorem C_value (W : ℕ → IntervalJet) :
    EqOn (C R W).value (coefficientC R) (Icc (0:ℝ) 1) := by
  intro t ht
  simp only [C,amplitude,JetExpr.value,velocity_value R W ht,
    root_value R W ht,k_value,coefficientC,referenceData,RationalReference.referenceData,pow_two]
/--
Pointwise equality on the specified domain: `EqOn (A R W).value (coefficientA R) (Icc (0:ℝ)
1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_filter_step` uses this pointwise
identity to establish membership in the specified domain/enclosure: `(referenceData
R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.velocity_value`
with the arguments shown in the proof.
-/
theorem A_value (W : ℕ → IntervalJet) :
    EqOn (A R W).value (coefficientA R) (Icc (0:ℝ) 1) := by
  intro t ht
  simp only [A,JetExpr.scale,JetExpr.value,velocity_value R W ht,coefficientA,Rat.cast_neg,Rat.cast_ofNat]
/--
Pointwise equality on the specified domain: `EqOn (B R W sigma).value (coefficientB R sigma)
(Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_filter_step` uses this pointwise
identity to establish membership in the specified domain/enclosure: `(referenceData
R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.velocity_value`
with the arguments shown in the proof.
-/
theorem B_value (W : ℕ → IntervalJet) (sigma : ℚ) :
    EqOn (B R W sigma).value (coefficientB R sigma) (Icc (0:ℝ) 1) := by
  intro t ht
  simp only [B,JetExpr.scale,JetExpr.value,velocity_value R W ht,coefficientB,Rat.cast_neg]

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (coefficientC R) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.flowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (coefficientC R) (coefficientA
R) (coefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.Regular.smooth`,
`«2610.05164v2».Numerics.ReferenceJetSource.C_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.C_value` with the arguments shown in the proof.
-/
theorem coefficientC_smooth : ContDiffOn ℝ ∞ (coefficientC R) (Icc (0:ℝ) 1) :=
  ((C_regular R (fun _ => [])).smooth).congr (C_value R (fun _ => [])).symm
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (coefficientA R) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.flowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (coefficientC R) (coefficientA
R) (coefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.Regular.smooth`,
`«2610.05164v2».Numerics.ReferenceJetSource.A_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.A_value` with the arguments shown in the proof.
-/
theorem coefficientA_smooth : ContDiffOn ℝ ∞ (coefficientA R) (Icc (0:ℝ) 1) :=
  ((A_regular R (fun _ => [])).smooth).congr (A_value R (fun _ => [])).symm
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (coefficientB R sigma) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.flowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (coefficientC R) (coefficientA
R) (coefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.Regular.smooth`,
`«2610.05164v2».Numerics.ReferenceJetSource.B_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.B_value` with the arguments shown in the proof.
-/
theorem coefficientB_smooth (sigma : ℚ) :
    ContDiffOn ℝ ∞ (coefficientB R sigma) (Icc (0:ℝ) 1) :=
  ((B_regular R (fun _ => []) sigma).smooth).congr (B_value R (fun _ => []) sigma).symm

/--
Defines `sourceCheck` of type `Bool` by `graphCheck R sigma W X N JC JA JB`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.flowSourceCheck` uses this definition in the
displayed construction of `flowSourceCheck`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Section 4.1.
-/
def sourceCheck (sigma : ℚ) (W : ℕ → IntervalJet) (X : IntervalRat) (N : ℕ)
    (JC JA JB : IntervalJet) : Bool := graphCheck R sigma W X N JC JA JB

/--
The precise assertion is `JetEncloses JC (coefficientC R) s x N ∧ JetEncloses JA (coefficientA
R) s x N ∧ JetEncloses JB (coefficientB R sigma) s x N`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.flowSourceCheck_coefficients` uses this
assertion to establish `W.Coefficients (coefficientC R) (coefficientA
R) (coefficientB R sigma) a`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.graphCheck_sound`,
`«2610.05164v2».Numerics.normalizedWithin_congr`,
`«2610.05164v2».Numerics.ReferenceJetSource.C_value` with the arguments shown in the proof.
-/
theorem sourceCheck_sound {sigma : ℚ} {W : ℕ → IntervalJet} {X : IntervalRat} {N : ℕ}
    {JC JA JB : IntervalJet} (h : sourceCheck R sigma W X N JC JA JB=true)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hsub : s⊆Icc (0:ℝ) 1)
    {x : ℝ} (hx : x∈s) (hX : x∈X) :
    JetEncloses JC (coefficientC R) s x N ∧
      JetEncloses JA (coefficientA R) s x N ∧ JetEncloses JB (coefficientB R sigma) s x N := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Numerics.ReferenceJetSource.graphCheck_sound`,
  -- `«2610.05164v2».Numerics.normalizedWithin_congr`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.C_value` with the arguments shown in the
  -- proof.
  have hg := graphCheck_sound h hs hsub hx hX
  exact ⟨fun j hj => by rw [← normalizedWithin_congr ((C_value R W).mono hsub) j hx];exact hg.1 j hj,
    fun j hj => by rw [← normalizedWithin_congr ((A_value R W).mono hsub) j hx];exact hg.2.1 j hj,
    fun j hj => by rw [← normalizedWithin_congr ((B_value R W sigma).mono hsub) j hx];exact hg.2.2 j hj⟩

/--
Defines `flowSourceCheck` of type `Bool` by `if hh : 0<W.width then decide (0≤a ∧ a+W.width≤1)
&& sourceCheck R sigma P (IntervalRat.singleton a) (W.order-1) W.pointC W.pointA W.pointB &&
sourceCheck R sigma H ⟨a,a+W.width,by linarith⟩ W.order W.wholeC W.wholeA W.wholeB else false`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_filter_step` rewrites with this
definition to establish membership in the specified domain/enclosure: `(referenceData
R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.
-/
def flowSourceCheck (sigma a : ℚ) (P H : ℕ → IntervalJet) (W : FlowStep) : Bool :=
  if hh : 0<W.width then
    decide (0≤a ∧ a+W.width≤1) &&
      sourceCheck R sigma P (IntervalRat.singleton a) (W.order-1) W.pointC W.pointA W.pointB &&
      sourceCheck R sigma H ⟨a,a+W.width,by linarith⟩ W.order W.wholeC W.wholeA W.wholeB
  else false

/--
The precise assertion is `W.Coefficients (coefficientC R) (coefficientA R) (coefficientB R
sigma) a`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_filter_step` uses this assertion to
establish membership in the specified domain/enclosure: `(referenceData R).normalizedFilter (σ
:= (sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.

Proof: Separate `0<W.width` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem flowSourceCheck_coefficients {sigma a : ℚ} {P H : ℕ → IntervalJet} {W : FlowStep}
    (hc : flowSourceCheck R sigma a P H W=true) :
    W.Coefficients (coefficientC R) (coefficientA R) (coefficientB R sigma) a := by
  -- Separate `0<W.width` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hh : 0<W.width
  · have hp : ((0≤a ∧ a+W.width≤1) ∧
        sourceCheck R sigma P (IntervalRat.singleton a) (W.order-1) W.pointC W.pointA W.pointB=true) ∧
        sourceCheck R sigma H ⟨a,a+W.width,by linarith⟩ W.order W.wholeC W.wholeA W.wholeB=true := by
      simpa only [flowSourceCheck,dite_eq_left hh,Bool.and_eq_true,decide_eq_true_eq] using hc
    have ha : (0:ℝ)≤a := by exact_mod_cast hp.1.1.1
    have hb : (a:ℝ)+W.width≤1 := by exact_mod_cast hp.1.1.2
    have hhr : (0:ℝ)<W.width := by exact_mod_cast hh
    have hsub : Icc (a:ℝ) (a+W.width)⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
    have hs : UniqueDiffOn ℝ (Icc (a:ℝ) (a+W.width)) := uniqueDiffOn_Icc (by linarith)
    refine ⟨((coefficientC_smooth R).mono hsub).of_le (by simp),
      ((coefficientA_smooth R).mono hsub).of_le (by simp),
      ((coefficientB_smooth R sigma).mono hsub).of_le (by simp),?_,?_⟩
    · intro j hj
      have hsrc := sourceCheck_sound R hp.1.2 hs hsub
        (show (a:ℝ)∈Icc (a:ℝ) (a+W.width) from ⟨le_rfl,by linarith⟩)
        (IntervalRat.mem_singleton a)
      exact ⟨hsrc.1 j (by omega),hsrc.2.1 j (by omega),hsrc.2.2 j (by omega)⟩
    · intro t ht j hj
      have hsrc := sourceCheck_sound R hp.2 hs hsub ht
        (show t∈(⟨a,a+W.width,by linarith⟩:IntervalRat) by
          simpa only [IntervalRat.mem_def,Rat.cast_add,Set.mem_Icc] using ht)
      exact ⟨hsrc.1 j (by omega),hsrc.2.1 j (by omega),hsrc.2.2 j (by omega)⟩
  · simp [flowSourceCheck,hh] at hc

/--
Membership in the specified domain/enclosure: `(referenceData R).normalizedFilter (σ :=
(sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Section 4.1.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem actual_filter_step {sigma a : ℚ} (hsigma : 0<sigma)
    {P H : ℕ → IntervalJet} {W : FlowStep}
    (hsource : flowSourceCheck R sigma a P H W=true) (hcheck : W.check=true)
    (hinitial : (referenceData R).normalizedFilter (σ := (sigma:ℝ))
      (by exact_mod_cast hsigma) a∈W.initial) :
    (referenceData R).normalizedFilter (σ := (sigma:ℝ))
      (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have hcoeff := flowSourceCheck_coefficients R hsource
  have hh : 0<W.width := by
    by_contra hn
    simp [flowSourceCheck,hn] at hsource
  have hparts := hsource
  simp only [flowSourceCheck,dite_eq_left hh,Bool.and_eq_true,decide_eq_true_eq] at hparts
  have ha : (0:ℝ)≤a := by exact_mod_cast hparts.1.1.1
  have hb : (a:ℝ)+W.width≤1 := by exact_mod_cast hparts.1.1.2
  have hsub : Icc (a:ℝ) (a+W.width)⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
  apply W.check_sound hcheck hcoeff.1 hcoeff.2.1 hcoeff.2.2.1 hcoeff.2.2.2.1 hcoeff.2.2.2.2
    (((referenceData R).normalizedFilter_smooth (σ := (sigma:ℝ))
      (by exact_mod_cast hsigma)).continuousOn.mono hsub) _ hinitial
  intro t ht
  have h := filter_ode R (fun _ => []) hsigma (hsub ⟨ht.1.le,ht.2.le⟩)
  rw [C_value R (fun _ => []) (hsub ⟨ht.1.le,ht.2.le⟩),
    A_value R (fun _ => []) (hsub ⟨ht.1.le,ht.2.le⟩),
    B_value R (fun _ => []) sigma (hsub ⟨ht.1.le,ht.2.le⟩)] at h
  exact h.hasDerivAt (Icc_mem_nhds (lt_of_le_of_lt ha ht.1) (ht.2.trans_le hb))

end ReferenceJetSource
end «2610.05164v2».Numerics
