import chebyshev2.Comparison.Regularity

/-!
Article: chebyshev2, Lemma 11.
Lemma 10's symmetry, transported through the actual inverse coordinate.
Use: `chebyshev2.Calibration.Data.comparisonDensity_reflection` feeds
`chebyshev2.DualCertificate.NormalizedCalibration.S_actual` (S actual).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)
variable (hΓ : ∀ q ∈ Icc (0:ℝ) 2, C.Gamma (2-q)=C.Gamma q)
include hκ hΓ

/--
Exact identity `C.amplitude κ (2-q)=C.amplitude κ q`.

Use: `chebyshev2.Calibration.Data.comparisonDensity_reflection` rewrites with this identity
to establish the identity `C.comparisonDensity hκ (-x)=C.comparisonDensity hκ x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem amplitude_reflection (q : ℝ) : C.amplitude κ (2-q)=C.amplitude κ q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · have hr : 2-q ∈ Ioo (0:ℝ) 2 := ⟨by linarith [hq.2],by linarith [hq.1]⟩
    apply C.amplitude_unique hκ hr (C.amplitude_spec hκ hq).1
    have he := (C.amplitude_spec hκ hq).2
    simpa only [constant,chebyshev2.Calibration.Q_reflection,hΓ q ⟨hq.1.le,hq.2.le⟩] using he
  · have hr : 2-q ∉ Ioo (0:ℝ) 2 := by
      intro hr
      exact hq ⟨by linarith [hr.2],by linarith [hr.1]⟩
    simp only [amplitude,ite_eq_right hq,ite_eq_right hr]

/--
Exact identity `C.speed κ (2-q)=C.speed κ q`.

Use: `chebyshev2.Calibration.Data.comparisonReciprocal_reflection` rewrites with this
identity to establish the identity `(C.comparisonSpeed hκ).reciprocal
(2-q)=(C.comparisonSpeed hκ).reciprocal q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_reflection`,
`chebyshev2.Calibration.Q_reflection` with the arguments shown in the proof.
-/
theorem speed_reflection (q : ℝ) : C.speed κ (2-q)=C.speed κ q := by rw [speed,speed,C.amplitude_reflection hκ hΓ,chebyshev2.Calibration.Q_reflection]

/--
Exact identity `(C.comparisonSpeed hκ).reciprocal (2-q)=(C.comparisonSpeed hκ).reciprocal q`.

Use: `chebyshev2.Calibration.Data.comparisonX_reflection` uses this identity to establish
exact identity `(C.comparisonSpeed hκ).X (2-q)=-(C.comparisonSpeed hκ).X q`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem comparisonReciprocal_reflection (q : ℝ) :
    (C.comparisonSpeed hκ).reciprocal (2-q)=(C.comparisonSpeed hκ).reciprocal q := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · have hr : 2-q ∈ Ioo (0:ℝ) 2 := ⟨by linarith [hq.2],by linarith [hq.1]⟩
    simp only [SpeedData.reciprocal,indicator_of_mem hq,indicator_of_mem hr]
    change (C.speed κ (2-q))⁻¹=(C.speed κ q)⁻¹
    rw [C.speed_reflection hκ hΓ]
  · have hr : 2-q ∉ Ioo (0:ℝ) 2 := by
      intro hr
      exact hq ⟨by linarith [hr.2],by linarith [hr.1]⟩
    simp only [SpeedData.reciprocal,indicator_of_notMem hq,indicator_of_notMem hr]

/--
Exact identity `(C.comparisonSpeed hκ).X (2-q)=-(C.comparisonSpeed hκ).X q`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_reflection` rewrites with this
identity to establish the identity `(C.comparisonSpeed hκ).q (-x)=2-(C.comparisonSpeed hκ).q
x`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.comparisonReciprocal_reflection` with the arguments shown in
the proof.
-/
theorem comparisonX_reflection (q : ℝ) :
    (C.comparisonSpeed hκ).X (2-q)=-(C.comparisonSpeed hκ).X q := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.Data.comparisonReciprocal_reflection` with the arguments shown
  -- in the proof.
  let S := C.comparisonSpeed hκ
  have h := intervalIntegral.integral_comp_sub_left (a := 1) (b := q) S.reciprocal 2
  have he : (∫ t in (1:ℝ)..q, S.reciprocal (2-t))=∫ t in (1:ℝ)..q, S.reciprocal t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact C.comparisonReciprocal_reflection hκ hΓ t
  rw [he] at h
  norm_num only at h
  rw [intervalIntegral.integral_symm (a := 1) (b := 2-q)] at h
  change S.X (2-q)=-S.X q
  dsimp only [SpeedData.X]
  linarith

/--
Exact identity `(C.comparisonSpeed hκ).q (-x)=2-(C.comparisonSpeed hκ).q x`.

Use: `chebyshev2.Calibration.Data.comparisonDensity_reflection` rewrites with this identity
to establish the identity `C.comparisonDensity hκ (-x)=C.comparisonDensity hκ x`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.comparisonX_reflection`,
`chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
`chebyshev2.PrescribedSpeed.SpeedData.q_two_right` with the arguments shown in the proof.
-/
theorem comparisonCoordinate_reflection (x : ℝ) :
    (C.comparisonSpeed hκ).q (-x)=2-(C.comparisonSpeed hκ).q x := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.comparisonX_reflection`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_two_right` with the arguments shown in the
  -- proof.
  let S := C.comparisonSpeed hκ
  have he : S.X 2=-S.X 0 := by simpa only [sub_zero] using C.comparisonX_reflection hκ hΓ 0
  rcases le_or_gt x (S.X 0) with hl | hl
  · rw [S.q_zero_left hl,S.q_two_right (by linarith)]
    norm_num
  · rcases le_or_gt (S.X 2) x with hr | hr
    · rw [S.q_two_right hr,S.q_zero_left (by linarith)]
      norm_num
    · have hx : x ∈ Icc (S.X 0) (S.X 2) := ⟨hl.le,hr.le⟩
      have hq : 2-S.q x ∈ Icc (0:ℝ) 2 := by
        constructor <;> linarith [(S.q_mem x).1,(S.q_mem x).2]
      have hi := S.q_X hq
      have hX : S.X (2-S.q x)=-x := by
        rw [C.comparisonX_reflection hκ hΓ,S.X_q hx]
      rw [hX] at hi
      exact hi

/--
Exact identity `C.comparisonDensity hκ (-x)=C.comparisonDensity hκ x`.

Use: `chebyshev2.Calibration.Data.rightFilter_reflection` uses this identity to establish
exact identity `C.rightFilter hκ s q=nonlinear s (C.comparisonDensity hκ) ((C.comparisonSpeed
hκ).X (2-q))`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.comparisonDensity_formula`,
`chebyshev2.Calibration.Data.comparisonCoordinate_reflection`,
`chebyshev2.Calibration.Data.amplitude_reflection` with the arguments shown in the proof.
-/
theorem comparisonDensity_reflection (x : ℝ) : C.comparisonDensity hκ (-x)=C.comparisonDensity hκ x := by
  rw [C.comparisonDensity_formula hκ,C.comparisonDensity_formula hκ,
    C.comparisonCoordinate_reflection hκ hΓ,C.amplitude_reflection hκ hΓ]

end
end chebyshev2.Calibration.Data
