import «2610.05164v2».DualCertificate.ComparisonContinuity
import «2610.05164v2».DualCertificate.Data
import «2610.05164v2».Comparison.Symmetry
import «2610.05164v2».Comparison.RightFilters

/-!
Article: 2610.05164v2, Theorem 3.6.
Lemma 16(i)-(ii): the actual normalized comparison states on both sides.
Use: `«2610.05164v2».DualCertificate.Data.normalization_calibration` feeds
`«2610.05164v2».DualCertificate.Data.normalized_residual_of_admissible` (normalized residual of
admissible).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.NormalizedCalibration
noncomputable section
open Set Real «2610.05164v2».Calibration «2610.05164v2».Filters
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (N : «2610.05164v2».DualCertificate.NormalizedCalibration)

/--
Defines `reflectedCubeMap` of type `Ioi (0:ℝ) × Icc (0:ℝ) 2` by `(p.1,⟨2-(p.2:ℝ)^3,Side.q_mem
Side.right p.2.property⟩)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.farFilter_joint_continuous` uses
this definition to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.farFilter p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.
-/
def reflectedCubeMap (p : ParameterDomain) : Ioi (0:ℝ) × Icc (0:ℝ) 2 :=
  (p.1,⟨2-(p.2:ℝ)^3,Side.q_mem Side.right p.2.property⟩)

/--
Continuity of the displayed function: `Continuous reflectedCubeMap`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.farFilter_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.farFilter p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem reflectedCubeMap_continuous : Continuous reflectedCubeMap := by
  apply continuous_fst.prodMk
  apply Continuous.subtype_mk
  exact continuous_const.sub ((continuous_subtype_val.comp continuous_snd).pow 3)

/--
Defines `farFilter` of type `ℝ` by `N.calibration.leftFilter hκ s (2-t^3)/(2-t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R` uses this definition in the
displayed construction of `R`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def farFilter {κ : ℝ} (hκ : 0<κ) (s t : ℝ) : ℝ :=
  N.calibration.leftFilter hκ s (2-t^3)/(2-t^3)

/--
Defines `farLinear` of type `ℝ` by `N.calibration.leftLinear hκ (2-t^3)/(2-t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero` uses this definition in the
displayed construction of `Rzero`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def farLinear {κ : ℝ} (hκ : 0<κ) (t : ℝ) : ℝ :=
  N.calibration.leftLinear hκ (2-t^3)/(2-t^3)

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.farFilter
p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R_joint_continuous` uses this
continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.R side p.1.property s p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.leftFilter_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.reflectedCubeMap_continuous`,
`«2610.05164v2».DualCertificate.cube_mem` with the arguments shown in the proof.
-/
theorem farFilter_joint_continuous {s : ℝ} (hs : 0≤s) :
    Continuous (fun p : ParameterDomain => N.farFilter p.1.property s p.2) := by
  have hf := (N.calibration.leftFilter_joint_continuous hs).comp reflectedCubeMap_continuous
  have hd : Continuous (fun p : ParameterDomain => 2-(p.2:ℝ)^3) :=
    continuous_const.sub ((continuous_subtype_val.comp continuous_snd).pow 3)
  exact hf.div hd (fun p => ne_of_gt (by linarith [(cube_mem p.2.property).2]))

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.farLinear
p.1.property p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_joint_continuous` uses this
continuity result to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.Rzero side p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.leftLinear_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.reflectedCubeMap_continuous`,
`«2610.05164v2».DualCertificate.cube_mem` with the arguments shown in the proof.
-/
theorem farLinear_joint_continuous :
    Continuous (fun p : ParameterDomain => N.farLinear p.1.property p.2) := by
  have hf := N.calibration.leftLinear_joint_continuous.comp reflectedCubeMap_continuous
  have hd : Continuous (fun p : ParameterDomain => 2-(p.2:ℝ)^3) :=
    continuous_const.sub ((continuous_subtype_val.comp continuous_snd).pow 3)
  exact hf.div hd (fun p => ne_of_gt (by linarith [(cube_mem p.2.property).2]))

/--
Defines `U` of type `ℝ` by `match side with | .left => N.leftU hκ s t | .right =>
κ/s*N.farFilter hκ s t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.U_joint_continuous` uses this
definition to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.U side p.1.property s p.2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def U (side : Side) {κ : ℝ} (hκ : 0<κ) (s t : ℝ) : ℝ := match side with
  | .left => N.leftU hκ s t
  | .right => κ/s*N.farFilter hκ s t

/--
Defines `theta` of type `ℝ` by `match side with | .left => N.leftTheta hκ t | .right =>
1-N.farLinear hκ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.theta_joint_continuous` uses this
definition to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.theta side p.1.property p.2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def theta (side : Side) {κ : ℝ} (hκ : 0<κ) (t : ℝ) : ℝ := match side with
  | .left => N.leftTheta hκ t
  | .right => 1-N.farLinear hκ t

/--
Defines `R` of type `ℝ` by `match side with | .left => N.farFilter hκ s t | .right =>
s/κ*N.leftU hκ s t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R_joint_continuous` uses this
definition to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.R side p.1.property s p.2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def R (side : Side) {κ : ℝ} (hκ : 0<κ) (s t : ℝ) : ℝ := match side with
  | .left => N.farFilter hκ s t
  | .right => s/κ*N.leftU hκ s t

/--
Defines `Rzero` of type `ℝ` by `match side with | .left => N.farLinear hκ t | .right =>
1-N.leftTheta hκ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_joint_continuous` uses this
definition to establish continuity of the displayed function: `Continuous (fun p :
ParameterDomain => N.Rzero side p.1.property p.2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def Rzero (side : Side) {κ : ℝ} (hκ : 0<κ) (t : ℝ) : ℝ := match side with
  | .left => N.farLinear hκ t
  | .right => 1-N.leftTheta hκ t

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.U side
p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
NormalizedCalibration.ParameterDomain => P.comparisonC N side p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftU_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.farFilter_joint_continuous` with the
arguments shown in the proof.
-/
theorem U_joint_continuous (side : Side) {s : ℝ} (hs : 0<s) :
    Continuous (fun p : ParameterDomain => N.U side p.1.property s p.2) := by
  cases side with
  | left => exact N.leftU_joint_continuous hs
  | right =>
    have hk : Continuous (fun p : ParameterDomain => (p.1:ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact (hk.div_const s).mul (N.farFilter_joint_continuous hs.le)

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.theta side
p.1.property p.2)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.comparisonC_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
NormalizedCalibration.ParameterDomain => P.comparisonC N side p.1.property p.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.farLinear_joint_continuous` with the
arguments shown in the proof.
-/
theorem theta_joint_continuous (side : Side) :
    Continuous (fun p : ParameterDomain => N.theta side p.1.property p.2) := by
  cases side with
  | left => exact N.leftTheta_joint_continuous
  | right => exact continuous_const.sub N.farLinear_joint_continuous

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.R side
p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => N.certificateB P side p.1.property ξ₀ ξ₁ χ τ p.2.1 p.2.2.1 p.2.2.2.1
p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.farFilter_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftU_joint_continuous` with the
arguments shown in the proof.
-/
theorem R_joint_continuous (side : Side) {s : ℝ} (hs : 0<s) :
    Continuous (fun p : ParameterDomain => N.R side p.1.property s p.2) := by
  cases side with
  | left => exact N.farFilter_joint_continuous hs.le
  | right =>
    have hk : Continuous (fun p : ParameterDomain => (p.1:ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact (continuous_const.div hk (fun p => p.1.property.ne')).mul (N.leftU_joint_continuous hs)

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.Rzero side
p.1.property p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_joint_continuous` uses
this continuity result to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => N.certificateB P side p.1.property ξ₀ ξ₁ χ τ p.2.1 p.2.2.1 p.2.2.2.1
p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.farLinear_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_joint_continuous` with the
arguments shown in the proof.
-/
theorem Rzero_joint_continuous (side : Side) :
    Continuous (fun p : ParameterDomain => N.Rzero side p.1.property p.2) := by
  cases side with
  | left => exact N.farLinear_joint_continuous
  | right => exact continuous_const.sub N.leftTheta_joint_continuous

/--
Membership in the specified domain/enclosure: `N.farFilter hκ s t∈Icc (0:ℝ) (s/κ)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R_range` uses this assertion to
establish membership in the specified domain/enclosure: `N.R side hκ s t∈Icc (0:ℝ) (s/κ)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».Calibration.Data.leftFilter_bounds`,
`«2610.05164v2».DualCertificate.Side.q_mem` with the arguments shown in the proof.
-/
theorem farFilter_range {κ s t : ℝ} (hκ : 0<κ) (hs : 0≤s) (ht : t∈Icc (0:ℝ) 1) :
    N.farFilter hκ s t∈Icc (0:ℝ) (s/κ) := by
  have hh : 0<2-t^3 := by linarith [(cube_mem ht).2]
  have hb := N.calibration.leftFilter_bounds hκ hs (Side.q_mem Side.right ht)
  exact ⟨div_nonneg hb.1 hh.le,(div_le_iff₀ hh).mpr hb.2⟩

/--
Membership in the specified domain/enclosure: `N.farLinear hκ t∈Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_range` uses this assertion to
establish membership in the specified domain/enclosure: `N.Rzero side hκ t∈Icc (0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».Calibration.Data.leftLinear_bounds`,
`«2610.05164v2».DualCertificate.Side.q_mem` with the arguments shown in the proof.
-/
theorem farLinear_range {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    N.farLinear hκ t∈Icc (0:ℝ) 1 := by
  have hh : 0<2-t^3 := by linarith [(cube_mem ht).2]
  have hb := N.calibration.leftLinear_bounds hκ (Side.q_mem Side.right ht)
  exact ⟨div_nonneg hb.1 hh.le,(div_le_one hh).mpr hb.2⟩

/--
Membership in the specified domain/enclosure: `N.U side hκ s t∈Icc (0:ℝ) 1`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.6.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem U_range (side : Side) {κ s t : ℝ} (hκ : 0<κ) (hs : 0<s) (ht : t∈Icc (0:ℝ) 1) :
    N.U side hκ s t∈Icc (0:ℝ) 1 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  cases side with
  | left => exact N.leftU_range hκ hs ht
  | right =>
    have hb := N.farFilter_range hκ hs.le ht
    have ha : 0≤κ/s := div_nonneg hκ.le hs.le
    refine ⟨mul_nonneg ha hb.1,?_⟩
    calc
      _ ≤ κ/s*(s/κ) := mul_le_mul_of_nonneg_left hb.2 ha
      _ = 1 := by field_simp

/--
Membership in the specified domain/enclosure: `N.theta side hκ t∈Icc (0:ℝ) 1`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.6.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_range`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.farLinear_range` with the arguments shown
in the proof.
-/
theorem theta_range (side : Side) {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    N.theta side hκ t∈Icc (0:ℝ) 1 := by
  cases side with
  | left => exact N.leftTheta_range hκ ht
  | right => change 1-N.farLinear hκ t∈Icc (0:ℝ) 1
             have hb := N.farLinear_range hκ ht
             exact ⟨by linarith [hb.2],by linarith [hb.1]⟩

/--
Membership in the specified domain/enclosure: `N.R side hκ s t∈Icc (0:ℝ) (s/κ)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.determinantTerm_denominator` uses
this assertion to prove the bound `2≤2+side.q t*(s/κ)*U+(2-side.q
t)*N.R side hκ s t`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.farFilter_range`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftU_range` with the arguments shown in
the proof.
-/
theorem R_range (side : Side) {κ s t : ℝ} (hκ : 0<κ) (hs : 0<s) (ht : t∈Icc (0:ℝ) 1) :
    N.R side hκ s t∈Icc (0:ℝ) (s/κ) := by
  cases side with
  | left => exact N.farFilter_range hκ hs.le ht
  | right =>
    have hb := N.leftU_range hκ hs ht
    have ha : 0≤s/κ := div_nonneg hs.le hκ.le
    exact ⟨mul_nonneg ha hb.1,mul_le_of_le_one_right ha hb.2⟩

/--
Membership in the specified domain/enclosure: `N.Rzero side hκ t∈Icc (0:ℝ) 1`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.6.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.farLinear_range`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_range` with the arguments shown
in the proof.
-/
theorem Rzero_range (side : Side) {κ t : ℝ} (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    N.Rzero side hκ t∈Icc (0:ℝ) 1 := by
  cases side with
  | left => exact N.farLinear_range hκ ht
  | right => change 1-N.leftTheta hκ t∈Icc (0:ℝ) 1
             have hb := N.leftTheta_range hκ ht
             exact ⟨by linarith [hb.2],by linarith [hb.1]⟩

variable (hΓ : ∀ q∈Icc (0:ℝ) 2, N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
Exact identity `N.calibration.rightFilter hκ s q=N.calibration.leftFilter hκ s (2-q)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R_factor` rewrites with this
identity to establish the identity `(2-side.q t)*N.R side hκ s t=N.calibration.rightFilter hκ
s (side.q t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightFilter_reflection {κ : ℝ} (hκ : 0<κ) (s q : ℝ) :
    N.calibration.rightFilter hκ s q=N.calibration.leftFilter hκ s (2-q) := by
  have hm : reflected (N.calibration.comparisonDensity hκ)=N.calibration.comparisonDensity hκ :=
    funext (N.calibration.comparisonDensity_reflection hκ hΓ)
  unfold «2610.05164v2».Calibration.Data.rightFilter «2610.05164v2».Calibration.Data.leftFilter
  rw [hm,N.calibration.comparisonX_reflection hκ hΓ]

include hΓ in
/--
Exact identity `N.calibration.rightLinear hκ q=N.calibration.leftLinear hκ (2-q)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_factor` rewrites with this
identity to establish the identity `(2-side.q t)*N.Rzero side hκ t=N.calibration.rightLinear
hκ (side.q t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightLinear_reflection {κ : ℝ} (hκ : 0<κ) (q : ℝ) :
    N.calibration.rightLinear hκ q=N.calibration.leftLinear hκ (2-q) := by
  have hm : reflected (N.calibration.comparisonDensity hκ)=N.calibration.comparisonDensity hκ :=
    funext (N.calibration.comparisonDensity_reflection hκ hΓ)
  unfold «2610.05164v2».Calibration.Data.rightLinear «2610.05164v2».Calibration.Data.leftLinear
  rw [hm,N.calibration.comparisonX_reflection hκ hΓ]

/--
Exact identity `t^3*N.leftU hκ s t=κ/s*N.calibration.leftFilter hκ s (t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.R_factor` uses this identity to
establish exact identity `(2-side.q t)*N.R side hκ s t=N.calibration.rightFilter hκ s (side.q
t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem leftU_factor {κ s t : ℝ} (hκ : 0<κ) (hs : 0<s) (ht : t∈Ioc (0:ℝ) 1) :
    t^3*N.leftU hκ s t=κ/s*N.calibration.leftFilter hκ s (t^3) := by
  rw [leftU,defectQuotient,ite_eq_right ht.1.ne']
  unfold defect filter
  field_simp [ht.1.ne',hκ.ne',hs.ne']
  ring

 /--
Exact identity `t^3*N.leftTheta hκ t=t^3-N.calibration.leftLinear hκ (t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_factor` uses this identity to
establish exact identity `(2-side.q t)*N.Rzero side hκ t=N.calibration.rightLinear hκ (side.q
t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem leftTheta_factor {κ t : ℝ} (hκ : 0<κ) (ht : t∈Ioc (0:ℝ) 1) :
    t^3*N.leftTheta hκ t=t^3-N.calibration.leftLinear hκ (t^3) := by
  rw [leftTheta,linearDefectQuotient,ite_eq_right ht.1.ne']
  unfold linearDefect linear
  field_simp [ht.1.ne']

end
end «2610.05164v2».DualCertificate.NormalizedCalibration

namespace «2610.05164v2».DualCertificate.Data
noncomputable section
variable (D : «2610.05164v2».DualCertificate.Data)

/--
Defines `normalization` of type `«2610.05164v2».DualCertificate.NormalizedCalibration` by
`«2610.05164v2».DualCertificate.referenceNormalizedCalibration D.referenceData (σ := (D.σ:ℝ))
(b := (D.b:ℝ)) (omega := (D.ω:ℝ)) (by exact_mod_cast D.σ_pos) (by exact_mod_cast D.b_pos) (by
exact_mod_cast D.ω_nonneg)`.

Use: `«2610.05164v2».DualCertificate.Data.normalization_calibration` uses this definition to
establish exact identity `D.normalization.calibration=D.calibration`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def normalization : «2610.05164v2».DualCertificate.NormalizedCalibration :=
  «2610.05164v2».DualCertificate.referenceNormalizedCalibration D.referenceData (σ := (D.σ:ℝ)) (b := (D.b:ℝ)) (omega := (D.ω:ℝ))
    (by exact_mod_cast D.σ_pos) (by exact_mod_cast D.b_pos) (by exact_mod_cast D.ω_nonneg)

/--
Exact identity `D.normalization.calibration=D.calibration`.

Use: `«2610.05164v2».DualCertificate.Data.normalized_residual_of_admissible` rewrites with this
identity to prove the quantified assertion `∀ n : ℝ,0≤n →
0≤D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential κ)
(PolynomialPotential.unnormalize κ (side.q t,U,V,θ)) n`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem normalization_calibration : D.normalization.calibration=D.calibration := rfl

end
end «2610.05164v2».DualCertificate.Data
