import chebyshev2.Numerics.IntegerResidualChain
import chebyshev2.Numerics.ReflectedReferenceSource

/-!
Article: chebyshev2, Section 4.1.
Discharging the analytic premises of the finite residual chain with the actual left and reflected
reference filters.
Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` feeds
`chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` (full trajectory).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate.ResidualCell
open Set chebyshev2.DualCertificate chebyshev2.Calibration
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `leftChartCheck` of type `Bool` by `decide (r.reflected=false ∧ 0≤r.start ∧
r.start+r.width≤s)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` uses
this definition to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def leftChartCheck (s : Nat) (r : Row) : Bool :=
  decide (r.reflected=false ∧ 0≤r.start ∧ r.start+r.width≤s)
/--
Defines `rightChartCheck` of type `Bool` by `decide (r.reflected=true ∧ (s:Int)≤r.start ∧
r.start+r.width≤2*s)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` uses
this definition to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rightChartCheck (s : Nat) (r : Row) : Bool :=
  decide (r.reflected=true ∧ (s:Int)≤r.start ∧ r.start+r.width≤2*s)

variable {s : Nat} (hs : 0<s) {ops : List Op} {piB : Bounds}
    (hpi : piB.Mem s Real.pi) (R : RationalReference) (σ η : ℚ)
    (shapeK : codeExpressionCheck ops 72 ResidualExpr.k=true)
    (shapeD : codeExpressionCheck ops 30 (ResidualExpr.profileParts R).1=true)
    (shapeRoot : codeExpressionCheck ops 16 (ResidualExpr.rootResidual R)=true)
    (shapeFactor : codeExpressionCheck ops 12 ResidualExpr.factor=true)
    (shapeODE : codeExpressionCheck ops 0 (ResidualExpr.odeResidual σ)=true)
    (hσ : 0<σ) (hη : 0≤η)

include hs hpi shapeK shapeD shapeRoot shapeFactor shapeODE hη

/--
The precise assertion is `Stable s (η:ℝ) ((ReferenceJetSource.referenceData R).normalizedFilter
(σ := (σ:ℝ)) (by exact_mod_cast hσ)) r`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` uses
this identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.error`,
`chebyshev2.Calibration.ReferenceData.normalizedFilter_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedFilter_bounds` with the arguments shown in
the proof.
-/
theorem left_stable (r : Row) (hc : check s ops piB η r=true)
    (hchart : leftChartCheck s r=true) :
    Stable s (η:ℝ) ((ReferenceJetSource.referenceData R).normalizedFilter
      (σ := (σ:ℝ)) (by exact_mod_cast hσ)) r := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.error`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedFilter_smooth`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedFilter_bounds` with the arguments
  -- shown in the proof.
  let D := ReferenceJetSource.referenceData R
  have hσr : (0:ℝ)<(σ:ℝ) := by exact_mod_cast hσ
  obtain ⟨href,hl,hu⟩ := of_decide_eq_true hchart
  have hsl : (0:ℝ)≤r.left s := by
    exact div_nonneg (by exact_mod_cast hl) (Nat.cast_nonneg s)
  have hsu : r.right s≤1 := by
    have hs' : (0:ℝ)<s := by exact_mod_cast hs
    rw [Row.right,div_le_iff₀ hs']
    simpa using (show (r.start:ℝ)+r.width≤(s:ℝ) by exact_mod_cast hu)
  have hsub : Icc (r.left s) (r.right s)⊆Icc (0:ℝ) 1 :=
    fun x hx => ⟨hsl.trans hx.1,hx.2.trans hsu⟩
  intro e he h0 t ht
  apply Row.error hs hpi R σ η shapeK shapeD shapeRoot shapeFactor shapeODE
    hσr.le (by exact_mod_cast hη) r hc ?_
    ((D.normalizedFilter_smooth hσr).continuousOn.mono hsub) ?_ ?_ he h0 ht
  · intro x hx
    simpa [Row.chart,href] using hsub hx
  · intro x hx
    exact (D.normalizedFilter_bounds hσr (hsub ⟨hx.1,hx.2.le⟩)).1
  · intro x hx
    have hx01 := hsub ⟨hx.1,hx.2.le⟩
    have hd := D.normalizedFilter_derivative hσr hx01
    have hd' := hd.mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE (hx.2.trans_le hsu))
        (fun z hz => And.intro (hx01.1.trans hz.1) hz.2))
    simpa [Row.chart,href,D,ReferenceJetSource.referenceData,RationalReference.referenceData] using hd'

/--
The precise assertion is `Stable s (η:ℝ) (ReferenceJetSource.rightFilter R hσ) r`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.complete_reference_chain` uses
this assertion to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.error`,
`chebyshev2.Numerics.ReferenceJetSource.rightFilter_smooth`,
`chebyshev2.Calibration.ReferenceData.filter_bounds` with the arguments shown in the proof.
-/
theorem right_stable (r : Row) (hc : check s ops piB η r=true)
    (hchart : rightChartCheck s r=true) :
    Stable s (η:ℝ) (ReferenceJetSource.rightFilter R hσ) r := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.error`,
  -- `chebyshev2.Numerics.ReferenceJetSource.rightFilter_smooth`,
  -- `chebyshev2.Calibration.ReferenceData.filter_bounds` with the arguments shown in the
  -- proof.
  let D := ReferenceJetSource.referenceData R
  have hσr : (0:ℝ)<(σ:ℝ) := by exact_mod_cast hσ
  obtain ⟨href,hl,hu⟩ := of_decide_eq_true hchart
  have hsl : (1:ℝ)≤r.left s := by
    have hs' : (0:ℝ)<s := by exact_mod_cast hs
    rw [Row.left,le_div_iff₀ hs']
    simpa using (show (s:ℝ)≤(r.start:ℝ) by exact_mod_cast hl)
  have hsu : r.right s≤2 := by
    have hs' : (0:ℝ)<s := by exact_mod_cast hs
    rw [Row.right,div_le_iff₀ hs']
    exact_mod_cast hu
  have hsub : Icc (r.left s) (r.right s)⊆Icc (1:ℝ) 2 :=
    fun x hx => ⟨hsl.trans hx.1,hx.2.trans hsu⟩
  intro e he h0 t ht
  apply Row.error hs hpi R σ η shapeK shapeD shapeRoot shapeFactor shapeODE
    hσr.le (by exact_mod_cast hη) r hc ?_
    ((ReferenceJetSource.rightFilter_smooth R hσ).continuousOn.mono hsub) ?_ ?_ he h0 ht
  · intro x hx
    simp only [Row.chart,href,↓reduceIte]
    have hh := hsub hx
    constructor <;> linarith [hh.1,hh.2]
  · intro x _
    exact (D.filter_bounds hσr (-D.normalizedX (2-x))).1
  · intro x hx
    have hx12 := hsub ⟨hx.1,hx.2.le⟩
    have hd := ReferenceJetSource.rightFilter_ode R hσ hx12
    have hd' := hd.mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE (hx.2.trans_le hsu))
        (fun z hz => And.intro (hx12.1.trans hz.1) hz.2))
    convert hd' using 1
    simp only [Row.chart,href,↓reduceIte,ReferenceJetSource.rightCoefficientC,
      ReferenceJetSource.rightCoefficientA,ReferenceJetSource.rightCoefficientB,
      ReferenceJetSource.coefficientC,ReferenceJetSource.coefficientA,
      ReferenceJetSource.coefficientB]
    dsimp [D,ReferenceJetSource.referenceData,RationalReference.referenceData]
    ring

/--
The stated quantitative bound `(∀ r∈leftRows, ∀ t∈Icc (r.left s) (r.right s),
|(ReferenceJetSource.referenceData R).normalizedFilter (σ := (σ:ℝ)) (by exact_mod_cast hσ)
t-r.approx s t|≤(leftBound:ℝ)) ∧ (∀ r∈rightRows, ∀ t∈Icc (r.left s) (r.right s),
|ReferenceJetSource.rightFilter R hσ t-r.approx s t|≤(rightBound:ℝ)) ∧
|ReferenceJetSource.rightFilter R hσ 2-(lastValue s (lastValue s 0 leftRows) rightRows:ℝ)|≤
(rightBound:ℝ)`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` uses this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.left_stable`,
`chebyshev2.Calibration.ReferenceData.normalizedFilter_zero`,
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.chain_sound` with the arguments shown
in the proof.
-/
theorem complete_reference_chain (leftRows rightRows : List Row) (leftBound rightBound : ℚ)
    (hchecks : ∀ r∈leftRows++rightRows, check s ops piB η r=true)
    (hleft : ∀ r∈leftRows, leftChartCheck s r=true)
    (hright : ∀ r∈rightRows, rightChartCheck s r=true)
    (hchainLeft : chainCheck s η leftBound s 0 0 0 leftRows=true)
    (hchainRight : chainCheck s η rightBound (2*s) s (lastValue s 0 leftRows)
      leftBound rightRows=true) :
    (∀ r∈leftRows, ∀ t∈Icc (r.left s) (r.right s),
      |(ReferenceJetSource.referenceData R).normalizedFilter (σ := (σ:ℝ))
        (by exact_mod_cast hσ) t-r.approx s t|≤(leftBound:ℝ)) ∧
    (∀ r∈rightRows, ∀ t∈Icc (r.left s) (r.right s),
      |ReferenceJetSource.rightFilter R hσ t-r.approx s t|≤(rightBound:ℝ)) ∧
    |ReferenceJetSource.rightFilter R hσ 2-(lastValue s (lastValue s 0 leftRows) rightRows:ℝ)|≤
      (rightBound:ℝ) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.ResidualCell.left_stable`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedFilter_zero`,
  -- `chebyshev2.Numerics.IntegerCertificate.ResidualCell.chain_sound` with the arguments
  -- shown in the proof.
  let D := ReferenceJetSource.referenceData R
  have hσr : (0:ℝ)<(σ:ℝ) := by exact_mod_cast hσ
  have hlstable (r : Row) (hr : r∈leftRows) :
      Stable s (η:ℝ) (D.normalizedFilter hσr) r :=
    left_stable hs hpi R σ η shapeK shapeD shapeRoot shapeFactor shapeODE hσ hη r
      (hchecks r (List.mem_append_left _ hr)) (hleft r hr)
  have hinit' : |D.normalizedFilter hσr (((0:Int):ℝ)/s)-((0:ℚ):ℝ)|≤((0:ℚ):ℝ) := by
    simp [D.normalizedFilter_zero hσr]
  have hl := chain_sound hs hη leftRows hchainLeft hlstable hinit'
  have hs' : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  have hrstable (r : Row) (hr : r∈rightRows) :
      Stable s (η:ℝ) (ReferenceJetSource.rightFilter R hσ) r :=
    right_stable hs hpi R σ η shapeK shapeD shapeRoot shapeFactor shapeODE hσ hη r
      (hchecks r (List.mem_append_right _ hr)) (hright r hr)
  have hmid' : |ReferenceJetSource.rightFilter R hσ (((s:Int):ℝ)/s)-
      (lastValue s 0 leftRows:ℝ)|≤(leftBound:ℝ) := by
    simpa [hs',ReferenceJetSource.rightFilter_one] using hl.1
  have hr := chain_sound hs hη rightRows hchainRight hrstable hmid'
  refine ⟨hl.2,hr.2,?_⟩
  simpa [hs',mul_div_cancel_right₀] using hr.1

end
end chebyshev2.Numerics.IntegerCertificate.ResidualCell
