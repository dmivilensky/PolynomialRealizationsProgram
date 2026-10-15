import «2610.05164v2».DualCertificate.ComparisonNormalization
import «2610.05164v2».Calculus.RegularFilter
import «2610.05164v2».Calculus.RegularDefect
import «2610.05164v2».Comparison.FilterContinuity
import «2610.05164v2».Comparison.LinearContinuity

/-!
Article: 2610.05164v2, Lemma 16.
F.1(F): the actual comparison filters and defects in the cubic coordinate.
Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient_smooth` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_smooth` (left Theta smooth).
Proof chain: `«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_smooth` — 2610.05164v2,
Lemma 16; Actual normalized coefficients, smooth endpoint quotients, state faces and centering.
-/
namespace «2610.05164v2».DualCertificate.NormalizedCalibration
noncomputable section
open Set Real «2610.05164v2».Calibration «2610.05164v2».Calculus
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (N : «2610.05164v2».DualCertificate.NormalizedCalibration) {κ s : ℝ} (hκ : 0<κ)

/--
Defines `velocity` of type `ℝ` by `3/N.speed κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_derivative` uses this
definition to establish the derivative within the stated domain: `HasDerivWithinAt (N.defect hκ
s) (defectRHS (N.velocity κ) (N.defect hκ s) (s/κ) t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def velocity (κ t : ℝ) : ℝ := 3/N.speed κ t
/--
Defines `filter` of type `ℝ` by `N.calibration.leftFilter hκ s (t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect` uses this definition in the
displayed construction of `defect`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def filter (s t : ℝ) : ℝ := N.calibration.leftFilter hκ s (t^3)
/--
Defines `linear` of type `ℝ` by `N.calibration.leftLinear hκ (t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect` uses this definition
in the displayed construction of `linearDefect`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def linear (t : ℝ) : ℝ := N.calibration.leftLinear hκ (t^3)
/--
Defines `defect` of type `ℝ` by `t^3-κ/s*N.filter hκ s t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient` uses this definition
in the displayed construction of `defectQuotient`. Its inputs and component formulas are fixed
by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def defect (s t : ℝ) : ℝ := t^3-κ/s*N.filter hκ s t
/--
Defines `linearDefect` of type `ℝ` by `t^3-N.linear hκ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient` uses this
definition in the displayed construction of `linearDefectQuotient`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def linearDefect (t : ℝ) : ℝ := t^3-N.linear hκ t

include hκ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.root κ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.filter_smooth` uses this assertion
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.filter hκ s) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth` with the arguments shown in
the proof.
-/
theorem root_smooth_fixed : ContDiffOn ℝ ∞ (N.root κ) (Icc (0:ℝ) 1) :=
  N.root_smooth.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht => ⟨hκ,ht⟩)

include hκ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.velocity κ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_cubic_quotient` uses this
assertion to construct witnesses satisfying `∃ g : ℝ → ℝ, ContDiffOn
ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.defect hκ s t=t^3*g t`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_positive` with the arguments shown
in the proof.
-/
theorem velocity_smooth : ContDiffOn ℝ ∞ (N.velocity κ) (Icc (0:ℝ) 1) :=
  contDiffOn_const.div
    (N.speed_smooth.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht => ⟨hκ,ht⟩))
    (fun _ ht => (N.speed_positive hκ ht).ne')

include hκ in
/--
The stated quantitative bound `0<N.velocity κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven` uses this bound
to construct witnesses satisfying `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1,
0≤N.defect hκ s t ∧ N.defect hκ s t≤C*t^7`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_positive` with the arguments shown
in the proof.
-/
theorem velocity_positive {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 0<N.velocity κ t :=
  div_pos (by norm_num) (N.speed_positive hκ ht)

/--
Continuity of the displayed function: `Continuous (N.filter hκ s)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.filter_smooth` uses this continuity
result to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.filter hκ s) (Icc (0:ℝ)
1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftFilter_continuous`
with the arguments shown in the proof.
-/
theorem filter_continuous (hs : 0≤s) : Continuous (N.filter hκ s) :=
  (N.calibration.leftFilter_continuous hκ hs).comp (by fun_prop)

/--
Continuity of the displayed function: `Continuous (N.linear hκ)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linear_smooth` uses this continuity
result to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.linear hκ) (Icc (0:ℝ)
1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_order_seven`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftLinear_continuous`
with the arguments shown in the proof.
-/
theorem linear_continuous : Continuous (N.linear hκ) :=
  (N.calibration.leftLinear_continuous hκ).comp (by fun_prop)

/--
Membership in the specified domain/enclosure: `t^3 ∈ Ioo (0:ℝ) 2`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_derivative` uses this
assertion to establish the derivative within the stated domain: `HasDerivWithinAt (N.defect hκ
s) (defectRHS (N.velocity κ) (N.defect hκ s) (s/κ) t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Side.q_interior` with the
arguments shown in the proof.
-/
theorem cube_interior {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : t^3 ∈ Ioo (0:ℝ) 2 :=
  Side.q_interior Side.left ⟨ht.1,ht.2.le⟩

/--
The actual derivative at the stated point: `HasDerivAt (N.filter hκ s) (N.velocity κ t*
(s*(t*N.root κ t)^2-2*N.filter hκ s t-(N.filter hκ s t)^2)) t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.filter_smooth` uses this derivative
formula to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.filter hκ s) (Icc (0:ℝ)
1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem filter_derivative (hs : 0≤s) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (N.filter hκ s) (N.velocity κ t*
      (s*(t*N.root κ t)^2-2*N.filter hκ s t-(N.filter hκ s t)^2)) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (N.calibration.leftFilter_derivative hκ hs (cube_interior ht)).comp
    (h := fun t : ℝ => t^3) t ((hasDerivAt_id t).pow 3)
  rw [N.root_amplitude hκ ⟨ht.1.le,ht.2.le⟩,N.speed_factor hκ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  dsimp only [velocity,filter,id_eq]
  field_simp [ht.1.ne',(N.speed_positive hκ ⟨ht.1.le,ht.2.le⟩).ne']
  ring

/--
The actual derivative at the stated point: `HasDerivAt (N.linear hκ) (N.velocity κ
t*(κ*(t*N.root κ t)^2-2*N.linear hκ t)) t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linear_smooth` uses this derivative
formula to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.linear hκ) (Icc (0:ℝ)
1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_order_seven`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem linear_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (N.linear hκ) (N.velocity κ t*(κ*(t*N.root κ t)^2-2*N.linear hκ t)) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (N.calibration.leftLinear_derivative hκ (cube_interior ht)).comp
    (h := fun t : ℝ => t^3) t ((hasDerivAt_id t).pow 3)
  rw [N.root_amplitude hκ ⟨ht.1.le,ht.2.le⟩,N.speed_factor hκ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  dsimp only [velocity,linear,id_eq]
  field_simp [ht.1.ne',(N.speed_positive hκ ⟨ht.1.le,ht.2.le⟩).ne']
  ring

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.filter hκ s) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_smooth` uses this assertion
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.defect hκ s) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.regular_filter_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth_fixed` with the arguments
shown in the proof.
-/
theorem filter_smooth (hs : 0≤s) : ContDiffOn ℝ ∞ (N.filter hκ s) (Icc (0:ℝ) 1) := by
  apply regular_filter_smooth (a := 1) (s := s) (N.velocity_smooth hκ) (N.root_smooth_fixed hκ)
    (N.filter_continuous hκ hs).continuousOn
  intro t ht
  simpa only [one_mul] using N.filter_derivative hκ hs ht

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.linear hκ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_smooth` uses this
assertion to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.linearDefect hκ) (Icc
(0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_order_seven`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.regular_filter_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth_fixed` with the arguments
shown in the proof.
-/
theorem linear_smooth : ContDiffOn ℝ ∞ (N.linear hκ) (Icc (0:ℝ) 1) := by
  apply regular_filter_smooth (s := κ) (a := 0) (N.velocity_smooth hκ) (N.root_smooth_fixed hκ)
    (N.linear_continuous hκ).continuousOn
  intro t ht
  simpa only [zero_mul,sub_zero] using N.linear_derivative hκ ht

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.defect hκ s) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_cubic_quotient` uses this
assertion to construct witnesses satisfying `∃ g : ℝ → ℝ, ContDiffOn
ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.defect hκ s t=t^3*g t`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.filter_smooth` with the arguments shown
in the proof.
-/
theorem defect_smooth (hs : 0<s) : ContDiffOn ℝ ∞ (N.defect hκ s) (Icc (0:ℝ) 1) :=
  (by fun_prop : ContDiffOn ℝ ∞ (fun t : ℝ => t^3) (Icc 0 1)).sub
    (contDiffOn_const.mul (N.filter_smooth hκ hs.le))

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.linearDefect hκ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_cubic_quotient` uses
this assertion to construct witnesses satisfying `∃ g : ℝ → ℝ,
ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.linearDefect hκ t=t^3*g t`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_order_seven`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.linear_smooth` with the arguments shown
in the proof.
-/
theorem linearDefect_smooth : ContDiffOn ℝ ∞ (N.linearDefect hκ) (Icc (0:ℝ) 1) :=
  (by fun_prop : ContDiffOn ℝ ∞ (fun t : ℝ => t^3) (Icc 0 1)).sub (N.linear_smooth hκ)

/--
The derivative within the stated domain: `HasDerivWithinAt (N.defect hκ s) (defectRHS
(N.velocity κ) (N.defect hκ s) (s/κ) t) (Icc (0:ℝ) 1) t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_cubic_quotient` uses this
derivative formula to construct witnesses satisfying `∃ g : ℝ → ℝ,
ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.defect hκ s t=t^3*g t`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem defect_derivative (hs : 0<s) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (N.defect hκ s) (defectRHS (N.velocity κ) (N.defect hκ s) (s/κ) t)
      (Icc (0:ℝ) 1) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hw := (N.defect_smooth hκ hs).continuousOn
  -- Establish continuity hg before using the function at limits or in calculus arguments.
  have hg : ContinuousOn (defectRHS (N.velocity κ) (N.defect hκ s) (s/κ)) (Icc (0:ℝ) 1) :=
    (N.velocity_smooth hκ).continuousOn.mul
      (((continuousOn_const.mul (continuousOn_id.pow 6)).sub
        ((continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.pow 3)))).mul hw)).add
        (continuousOn_const.mul (hw.pow 2)))
  apply hasDerivWithinAt_Icc_of_continuous_derivative (by norm_num) hw hg _ t ht
  intro t ht
  have h := (N.calibration.leftDefect_derivative hκ hs (cube_interior ht)).comp
    (h := fun t : ℝ => t^3) t ((hasDerivAt_id t).pow 3)
  rw [N.speed_factor hκ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  dsimp only [«2610.05164v2».Calibration.Data.leftDefect,defectRHS,velocity,defect,filter,id_eq]
  field_simp [ht.1.ne',(N.speed_positive hκ ⟨ht.1.le,ht.2.le⟩).ne']
  ring

/--
The derivative within the stated domain: `HasDerivWithinAt (N.linearDefect hκ) (defectRHS
(N.velocity κ) (N.linearDefect hκ) 0 t) (Icc (0:ℝ) 1) t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_cubic_quotient` uses
this derivative formula to construct witnesses satisfying `∃ g : ℝ →
ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.linearDefect hκ t=t^3*g t`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_order_seven`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem linearDefect_derivative {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (N.linearDefect hκ) (defectRHS (N.velocity κ) (N.linearDefect hκ) 0 t)
      (Icc (0:ℝ) 1) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hw := (N.linearDefect_smooth hκ).continuousOn
  -- Establish continuity hg before using the function at limits or in calculus arguments.
  have hg : ContinuousOn (defectRHS (N.velocity κ) (N.linearDefect hκ) 0) (Icc (0:ℝ) 1) := by
    unfold defectRHS
    simp only [add_zero,zero_mul,one_mul]
    exact (N.velocity_smooth hκ).continuousOn.mul
      ((continuousOn_id.pow 6).sub (continuousOn_const.mul hw))
  apply hasDerivWithinAt_Icc_of_continuous_derivative (by norm_num) hw hg _ t ht
  intro t ht
  have h := (N.calibration.leftLinearDefect_derivative hκ (cube_interior ht)).comp
    (h := fun t : ℝ => t^3) t ((hasDerivAt_id t).pow 3)
  rw [N.speed_factor hκ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  dsimp only [«2610.05164v2».Calibration.Data.leftLinearDefect,defectRHS,velocity,linearDefect,linear,id_eq]
  field_simp [ht.1.ne',(N.speed_positive hκ ⟨ht.1.le,ht.2.le⟩).ne']
  ring

/--
Exact identity `N.defect hκ s 0=0`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_cubic_quotient` uses this
identity to construct witnesses satisfying `∃ g : ℝ → ℝ, ContDiffOn ℝ
∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.defect hκ s t=t^3*g t`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftFilter_zero` with the
arguments shown in the proof.
-/
theorem defect_zero (hs : 0<s) : N.defect hκ s 0=0 := by simp [defect,filter,N.calibration.leftFilter_zero hκ hs.le]

/--
Exact identity `N.linearDefect hκ 0=0`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_cubic_quotient` uses
this identity to construct witnesses satisfying `∃ g : ℝ → ℝ,
ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.linearDefect hκ t=t^3*g t`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_order_seven`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftLinear_zero` with the
arguments shown in the proof.
-/
theorem linearDefect_zero : N.linearDefect hκ 0=0 := by simp [linearDefect,linear,N.calibration.leftLinear_zero hκ]

/--
Constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀
t ∈ Icc (0:ℝ) 1, N.defect hκ s t=t^3*g t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_smooth` uses this
identity to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.defectQuotient hκ s)
(Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.R_smooth`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.regular_defect_cubic_quotient`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_smooth` with the arguments shown
in the proof.
-/
theorem defect_cubic_quotient (hs : 0<s) :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧
      ∀ t ∈ Icc (0:ℝ) 1, N.defect hκ s t=t^3*g t :=
  regular_defect_cubic_quotient (N.velocity_smooth hκ) (N.defect_smooth hκ hs)
    (N.defect_zero hκ hs) (fun _ ht => N.defect_derivative hκ hs ht)

/--
Constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀
t ∈ Icc (0:ℝ) 1, N.linearDefect hκ t=t^3*g t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient_smooth` uses
this identity to establish smoothness to the stated order: `ContDiffOn ℝ ∞
(N.linearDefectQuotient hκ) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_smooth`.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.regular_defect_cubic_quotient`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_smooth` with the arguments
shown in the proof.
-/
theorem linearDefect_cubic_quotient :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧
      ∀ t ∈ Icc (0:ℝ) 1, N.linearDefect hκ t=t^3*g t :=
  regular_defect_cubic_quotient (N.velocity_smooth hκ) (N.linearDefect_smooth hκ)
    (N.linearDefect_zero hκ) (fun _ ht => N.linearDefect_derivative hκ ht)

/--
Membership in the specified domain/enclosure: `N.defect hκ s t ∈ Icc (0:ℝ) (t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven` uses this
assertion to construct witnesses satisfying `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc
(0:ℝ) 1, 0≤N.defect hκ s t ∧ N.defect hκ s t≤C*t^7`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftDefect_bounds`,
`«2610.05164v2».DualCertificate.cube_mem` with the arguments shown in the proof.
-/
theorem defect_bounds (hs : 0<s) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    N.defect hκ s t ∈ Icc (0:ℝ) (t^3) :=
  N.calibration.leftDefect_bounds hκ hs
    ⟨(cube_mem ht).1,(cube_mem ht).2.trans (by norm_num)⟩
/--
Membership in the specified domain/enclosure: `N.linearDefect hκ t ∈ Icc (0:ℝ) (t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefect_order_seven` uses this
assertion to construct witnesses satisfying `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc
(0:ℝ) 1, 0≤N.linearDefect hκ t ∧ N.linearDefect hκ t≤C*t^7`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftLinearDefect_bounds`,
`«2610.05164v2».DualCertificate.cube_mem` with the arguments shown in the proof.
-/
theorem linearDefect_bounds {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    N.linearDefect hκ t ∈ Icc (0:ℝ) (t^3) :=
  N.calibration.leftLinearDefect_bounds hκ
    ⟨(cube_mem ht).1,(cube_mem ht).2.trans (by norm_num)⟩
/--
Constructs witnesses with the exact properties `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1, 0≤N.defect hκ
s t ∧ N.defect hκ s t≤C*t^7`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_smooth` uses this
bound to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.defectQuotient hκ s) (Icc
(0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.defect_order_seven`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_positive` with the arguments
shown in the proof.
-/
theorem defect_order_seven (hs : 0<s) :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1, 0≤N.defect hκ s t ∧ N.defect hκ s t≤C*t^7 := by
  apply «2610.05164v2».Calculus.defect_order_seven (div_nonneg hs.le hκ.le)
    (N.velocity_smooth hκ).continuousOn (fun _ ht => (N.velocity_positive hκ ht).le)
    (N.defect_smooth hκ hs).continuousOn (N.defect_zero hκ hs)
    (fun _ ht => N.defect_bounds hκ hs ht)
  intro t ht
  exact (N.defect_derivative hκ hs ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/--
Constructs witnesses with the exact properties `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1,
0≤N.linearDefect hκ t ∧ N.linearDefect hκ t≤C*t^7`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient_smooth` uses
this bound to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.linearDefectQuotient
hκ) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.defect_order_seven`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_positive` with the arguments
shown in the proof.
-/
theorem linearDefect_order_seven :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1, 0≤N.linearDefect hκ t ∧ N.linearDefect hκ t≤C*t^7 := by
  apply «2610.05164v2».Calculus.defect_order_seven (a := 0) (by norm_num)
    (N.velocity_smooth hκ).continuousOn (fun _ ht => (N.velocity_positive hκ ht).le)
    (N.linearDefect_smooth hκ).continuousOn (N.linearDefect_zero hκ)
    (fun _ ht => N.linearDefect_bounds hκ ht)
  intro t ht
  exact (N.linearDefect_derivative hκ ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/--
Defines `defectQuotient` of type `ℝ` by `if t=0 then 0 else N.defect hκ s t/t^3`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_smooth` rewrites with
this definition to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.defectQuotient
hκ s) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def defectQuotient (s t : ℝ) : ℝ := if t=0 then 0 else N.defect hκ s t/t^3

/--
Defines `linearDefectQuotient` of type `ℝ` by `if t=0 then 0 else N.linearDefect hκ t/t^3`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.linearDefectQuotient_smooth`
rewrites with this definition to establish smoothness to the stated order: `ContDiffOn ℝ ∞
(N.linearDefectQuotient hκ) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def linearDefectQuotient (t : ℝ) : ℝ := if t=0 then 0 else N.linearDefect hκ t/t^3

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.defectQuotient hκ s) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.leftU_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.leftU hκ s) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.R_smooth`.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem defectQuotient_smooth (hs : 0<s) :
    ContDiffOn ℝ ∞ (N.defectQuotient hκ s) (Icc (0:ℝ) 1) := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  obtain ⟨g,hg,hfactor⟩ := N.defect_cubic_quotient hκ hs
  obtain ⟨C,_,hC⟩ := N.defect_order_seven hκ hs
  have hz := cubic_quotient_zero_of_order_seven hg.continuousOn hfactor hC
  apply hg.congr
  intro t ht
  by_cases he : t=0
  · simp [defectQuotient,he,hz]
  · rw [defectQuotient,ite_eq_right he,hfactor t ht]
    field_simp

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.linearDefectQuotient hκ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.leftTheta_smooth` uses this
assertion to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.leftTheta hκ) (Icc
(0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.Rzero_smooth`.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem linearDefectQuotient_smooth :
    ContDiffOn ℝ ∞ (N.linearDefectQuotient hκ) (Icc (0:ℝ) 1) := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  obtain ⟨g,hg,hfactor⟩ := N.linearDefect_cubic_quotient hκ
  obtain ⟨C,_,hC⟩ := N.linearDefect_order_seven hκ
  have hz := cubic_quotient_zero_of_order_seven hg.continuousOn hfactor hC
  apply hg.congr
  intro t ht
  by_cases he : t=0
  · simp [linearDefectQuotient,he,hz]
  · rw [linearDefectQuotient,ite_eq_right he,hfactor t ht]
    field_simp

end
end «2610.05164v2».DualCertificate.NormalizedCalibration
