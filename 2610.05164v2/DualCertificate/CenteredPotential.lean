import «2610.05164v2».DualCertificate.ComparisonCurve
import «2610.05164v2».Calculus.CubicSides

/-!
Article: 2610.05164v2, Lemma 16.
Definition 7's centering uses the actual comparison filters.
Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centered_boundary` feeds
`«2610.05164v2».DualCertificate.Data.potential_boundary` (potential boundary).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.PolynomialPotential
noncomputable section
open Set «2610.05164v2».Residual «2610.05164v2».Calculus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (P : «2610.05164v2».DualCertificate.PolynomialPotential) (N : NormalizedCalibration)

/--
Defines `sideSlope` of type `ℝ` by `t*(N.root κ t)^3/N.speed κ t*P.comparisonC N side hκ t`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope` uses this definition in
the displayed construction of `curveSlope`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def sideSlope (side : Side) {κ : ℝ} (hκ : 0<κ) (t : ℝ) : ℝ :=
  t*(N.root κ t)^3/N.speed κ t*P.comparisonC N side hκ t

/--
Continuity on the stated domain: `ContinuousOn (P.comparisonC N side hκ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.sideSlope_continuous` uses this
continuity result to establish continuity on the stated domain: `ContinuousOn (P.sideSlope N
side hκ) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC_joint_continuous` with the
arguments shown in the proof.
-/
theorem comparisonC_continuous (side : Side) {κ : ℝ} (hκ : 0<κ) :
    ContinuousOn (P.comparisonC N side hκ) (Icc (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (P.comparisonC_joint_continuous N side).comp
    ((continuous_const (y := (⟨κ,hκ⟩ : Ioi (0:ℝ)))).prodMk continuous_id)

/--
Continuity on the stated domain: `ContinuousOn (P.sideSlope N side hκ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_continuous` uses this
continuity result to establish continuity on the stated domain: `ContinuousOn (P.curveSlope N
hκ) (Icc 0 2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_positive` with the arguments shown
in the proof.
-/
theorem sideSlope_continuous (side : Side) {κ : ℝ} (hκ : 0<κ) :
    ContinuousOn (P.sideSlope N side hκ) (Icc (0:ℝ) 1) := by
  have hr := N.root_smooth.continuousOn.comp
    (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hκ,ht⟩)
  have hd := N.speed_smooth.continuousOn.comp
    (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hκ,ht⟩)
  exact ((continuousOn_id.mul (hr.pow 3)).div hd
    (fun _ ht => (N.speed_positive hκ ht).ne')).mul (P.comparisonC_continuous N side hκ)

 /--
Exact identity `P.sideSlope N side hκ 0=0`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_two` rewrites with this
identity to establish the identity `P.curveSlope N hκ 2=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sideSlope_zero (side : Side) {κ : ℝ} (hκ : 0<κ) : P.sideSlope N side hκ 0=0 := by simp [sideSlope]

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
Exact identity `P.sideSlope N Side.left hκ 1=P.sideSlope N Side.right hκ 1`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_continuous` uses this
identity to establish continuity on the stated domain: `ContinuousOn (P.curveSlope N hκ) (Icc 0
2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_normalized_derivative` with the
arguments shown in the proof.
-/
theorem sideSlope_midpoint {κ : ℝ} (hκ : 0<κ) :
    P.sideSlope N Side.left hκ 1=P.sideSlope N Side.right hκ 1 := by
  have hl := P.curveValue_normalized_derivative N hΓ Side.left hκ (by norm_num : (1:ℝ)∈Ioc 0 1)
  have hr := P.curveValue_normalized_derivative N hΓ Side.right hκ (by norm_num : (1:ℝ)∈Ioc 0 1)
  norm_num only [Side.q,one_pow,show (2:ℝ)-1=1 by norm_num] at hl hr
  exact hl.unique hr

/--
Defines `curveSlope` of type `ℝ → ℝ` by `cubicSides (P.sideSlope N Side.left hκ) (P.sideSlope N
Side.right hκ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_two` rewrites with this
definition to establish the identity `P.curveSlope N hκ 2=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def curveSlope {κ : ℝ} (hκ : 0<κ) : ℝ → ℝ :=
  cubicSides (P.sideSlope N Side.left hκ) (P.sideSlope N Side.right hκ)

include hΓ in
/--
Continuity on the stated domain: `ContinuousOn (P.curveSlope N hκ) (Icc 0 2)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centering_c1` uses this continuity
result to establish smoothness to the stated order: `ContDiff ℝ 1 (P.centering N hκ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubicSides_continuous`,
`«2610.05164v2».DualCertificate.PolynomialPotential.sideSlope_continuous`,
`«2610.05164v2».DualCertificate.PolynomialPotential.sideSlope_midpoint` with the arguments
shown in the proof.
-/
theorem curveSlope_continuous {κ : ℝ} (hκ : 0<κ) :
    ContinuousOn (P.curveSlope N hκ) (Icc 0 2) :=
  cubicSides_continuous (P.sideSlope_continuous N Side.left hκ)
    (P.sideSlope_continuous N Side.right hκ) (P.sideSlope_midpoint N hΓ hκ)

/--
Exact identity `P.curveSlope N hκ 0=0`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centering_c1` uses this identity to
establish smoothness to the stated order: `ContDiff ℝ 1 (P.centering N hκ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubicSides_zero`,
`«2610.05164v2».DualCertificate.PolynomialPotential.sideSlope_zero` with the arguments shown in
the proof.
-/
theorem curveSlope_zero {κ : ℝ} (hκ : 0<κ) : P.curveSlope N hκ 0=0 := by rw [curveSlope,cubicSides_zero,P.sideSlope_zero]

/--
Exact identity `P.curveSlope N hκ 2=0`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centering_c1` uses this identity to
establish smoothness to the stated order: `ContDiff ℝ 1 (P.centering N hκ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubicSides_two`,
`«2610.05164v2».DualCertificate.PolynomialPotential.sideSlope_zero` with the arguments shown in
the proof.
-/
theorem curveSlope_two {κ : ℝ} (hκ : 0<κ) : P.curveSlope N hκ 2=0 := by rw [curveSlope,cubicSides_two,P.sideSlope_zero]

include hΓ in
/--
The actual derivative at the stated point: `HasDerivAt (P.curveValue N hκ) (P.curveSlope N hκ
q) q`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_closed_derivative` uses
this derivative formula to prove the quantified assertion `∀ q∈Icc
(0:ℝ) 2, HasDerivWithinAt (P.curveValue N hκ) (P.curveSlope N hκ q) (Icc 0 2) q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `q≤1` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem curveValue_derivative_extended {κ q : ℝ} (hκ : 0<κ) (hq : q∈Ioo (0:ℝ) 2) :
    HasDerivAt (P.curveValue N hκ) (P.curveSlope N hκ q) q := by
  -- Separate `q≤1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hl : q≤1
  · have ht : cubeRoot q∈Ioc (0:ℝ) 1 := ⟨cubeRoot_pos hq.1,(cubeRoot_mem ⟨hq.1.le,hl⟩).2⟩
    have h := P.curveValue_normalized_derivative N hΓ Side.left hκ ht
    simpa only [curveSlope,cubicSides,ite_eq_left hl,Side.q,cubeRoot_cube hq.1.le,sideSlope] using h
  · have ht : cubeRoot (2-q)∈Ioc (0:ℝ) 1 :=
      ⟨cubeRoot_pos (by linarith [hq.2]),(cubeRoot_mem ⟨by linarith [hq.2],by linarith⟩).2⟩
    have h := P.curveValue_normalized_derivative N hΓ Side.right hκ ht
    simpa only [curveSlope,cubicSides,ite_eq_right hl,Side.q,
      cubeRoot_cube (by linarith [hq.2] : 0≤2-q),sub_sub_cancel,sideSlope] using h

 /--
Continuity on the stated domain: `ContinuousOn (P.curveValue N hκ) (Icc 0 2)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_closed_derivative` uses
this continuity result to prove the quantified assertion `∀ q∈Icc
(0:ℝ) 2, HasDerivWithinAt (P.curveValue N hκ) (P.curveSlope N hκ q) (Icc 0 2) q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.curve_continuous` with the arguments
shown in the proof.
-/
theorem curveValue_continuous {κ : ℝ} (hκ : 0<κ) :
    ContinuousOn (P.curveValue N hκ) (Icc 0 2) :=
  P.raw_smooth.continuous.comp_continuousOn (N.curve_continuous hκ)

 /--
Exact identity `P.curveValue N hκ 0=0`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centered_boundary` rewrites with this
identity to establish the identity `P.centered N hκ (0,0,0,0)=P.centered N hκ (2,0,0,2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.curve_zero`,
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_left` with the arguments shown in the
proof.
-/
theorem curveValue_zero {κ : ℝ} (hκ : 0<κ) : P.curveValue N hκ 0=0 := by rw [curveValue,N.curve_zero,P.raw_left]

 /--
Exact identity `P.curveValue N hκ 2=0`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centered_boundary` rewrites with this
identity to establish the identity `P.centered N hκ (0,0,0,0)=P.centered N hκ (2,0,0,2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_right` with the arguments shown in the
proof.
-/
theorem curveValue_two {κ : ℝ} (hκ : 0<κ) : P.curveValue N hκ 2=0 :=
  P.raw_right _ _ _

/--
Defines `centering` of type `ℝ → ℝ` by `zeroExtension 0 2 (P.curveValue N hκ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centered` uses this definition in the
displayed construction of `centered`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def centering {κ : ℝ} (hκ : 0<κ) : ℝ → ℝ := zeroExtension 0 2 (P.curveValue N hκ)

/--
Defines `centered` of type `State → ℝ` by `gaugePotential P.raw (P.centering N hκ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centered_boundary` uses this
definition to establish the identity `P.centered N hκ (0,0,0,0)=P.centered N hκ (2,0,0,2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def centered {κ : ℝ} (hκ : 0<κ) : State → ℝ := gaugePotential P.raw (P.centering N hκ)

include hΓ in
/--
Establishes the uniform, quantified assertion `∀ q∈Icc (0:ℝ) 2, HasDerivWithinAt (P.curveValue
N hκ) (P.curveSlope N hκ q) (Icc 0 2) q`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centering_c1` uses this assertion to
establish smoothness to the stated order: `ContDiff ℝ 1 (P.centering N hκ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.hasDerivWithinAt_Icc_of_continuous_derivative`,
`«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_continuous`,
`«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_continuous` with the arguments
shown in the proof.
-/
theorem curveValue_closed_derivative {κ : ℝ} (hκ : 0<κ) :
    ∀ q∈Icc (0:ℝ) 2, HasDerivWithinAt (P.curveValue N hκ) (P.curveSlope N hκ q) (Icc 0 2) q :=
  hasDerivWithinAt_Icc_of_continuous_derivative (by norm_num) (P.curveValue_continuous N hκ)
    (P.curveSlope_continuous N hΓ hκ) (fun _ hq => P.curveValue_derivative_extended N hΓ hκ hq)

include hΓ in
/--
The actual derivative at the stated point: `HasDerivAt (P.centering N hκ) (zeroExtension 0 2
(P.curveSlope N hκ) q) q`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 16.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.zeroExtension_hasDerivAt`,
`«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_closed_derivative`,
`«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_zero` with the arguments shown
in the proof.
-/
theorem centering_hasDerivAt {κ : ℝ} (hκ : 0<κ) (q : ℝ) :
    HasDerivAt (P.centering N hκ) (zeroExtension 0 2 (P.curveSlope N hκ) q) q :=
  zeroExtension_hasDerivAt (by norm_num) (P.curveValue_closed_derivative N hΓ hκ)
    (P.curveValue_zero N hκ) (P.curveValue_two N hκ) (P.curveSlope_zero N hκ) (P.curveSlope_two N hκ) q

include hΓ in
/--
Smoothness to the stated order: `ContDiff ℝ 1 (P.centering N hκ)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.centered_c1` uses this assertion to
establish smoothness to the stated order: `ContDiff ℝ 1 (P.centered N hκ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.zeroExtension_c1`,
`«2610.05164v2».DualCertificate.PolynomialPotential.curveSlope_continuous`,
`«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_closed_derivative` with the
arguments shown in the proof.
-/
theorem centering_c1 {κ : ℝ} (hκ : 0<κ) : ContDiff ℝ 1 (P.centering N hκ) :=
  zeroExtension_c1 (by norm_num) (P.curveSlope_continuous N hΓ hκ)
    (P.curveValue_closed_derivative N hΓ hκ) (P.curveValue_zero N hκ) (P.curveValue_two N hκ)
    (P.curveSlope_zero N hκ) (P.curveSlope_two N hκ)

include hΓ in
/--
Smoothness to the stated order: `ContDiff ℝ 1 (P.centered N hκ)`.

Use: `«2610.05164v2».DualCertificate.Data.potential_c1` uses this assertion to establish
smoothness to the stated order: `ContDiff ℝ 1 (D.statePotential κ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.gaugePotential_c1`,
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_smooth`,
`«2610.05164v2».DualCertificate.PolynomialPotential.centering_c1` with the arguments shown in
the proof.
-/
theorem centered_c1 {κ : ℝ} (hκ : 0<κ) : ContDiff ℝ 1 (P.centered N hκ) :=
  gaugePotential_c1 (P.raw_smooth.of_le (by simp)) (P.centering_c1 N hΓ hκ)

/--
Exact identity `P.centered N hκ (N.curve hκ q)=0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 16.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem centered_on_curve {κ q : ℝ} (hκ : 0<κ) (hq : q∈Icc (0:ℝ) 2) :
    P.centered N hκ (N.curve hκ q)=0 := by
  unfold centered gaugePotential centering
  rw [show (N.curve hκ q).1=q from rfl,zeroExtension,indicator_of_mem hq]
  exact sub_self _

/--
Exact identity `P.centered N hκ (0,0,0,0)=P.centered N hκ (2,0,0,2)`.

Use: `«2610.05164v2».DualCertificate.Data.potential_boundary` uses this identity to establish
exact identity `D.statePotential κ (0,0,0,0)=D.statePotential κ (2,0,0,2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_left`,
`«2610.05164v2».DualCertificate.PolynomialPotential.curveValue_zero`,
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_right` with the arguments shown in the
proof.
-/
theorem centered_boundary {κ : ℝ} (hκ : 0<κ) :
    P.centered N hκ (0,0,0,0)=P.centered N hκ (2,0,0,2) := by
  unfold centered gaugePotential centering
  simp only [zeroExtension,indicator_of_mem (by norm_num : (0:ℝ)∈Icc 0 2),
    indicator_of_mem (by norm_num : (2:ℝ)∈Icc 0 2),P.raw_left,P.raw_right,
    P.curveValue_zero N hκ,P.curveValue_two N hκ]

end
end «2610.05164v2».DualCertificate.PolynomialPotential
