import «2610.05164v2».Comparison.RightFilters

/-!
Article: 2610.05164v2, Lemma 11.
Left filters of the actual comparison density in ground coordinates.
Use: `«2610.05164v2».Calibration.Data.leftLinear_ac` feeds
`«2610.05164v2».Calibration.Data.leftLinearDefect_endpoint_bound` (left Linear Defect endpoint
bound).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Comparison
set_option backward.isDefEq.respectTransparency false
variable (C : «2610.05164v2».Calibration.Data) {κ : ℝ} (hκ : 0 < κ)

/--
Defines `leftFilter` of type `ℝ` by `nonlinear s (C.comparisonDensity hκ) ((C.comparisonSpeed
hκ).X q)`.

Use: `«2610.05164v2».Calibration.Data.leftFilter_derivative` uses this definition to establish
the actual derivative at the stated point: `HasDerivAt (C.leftFilter hκ s) ((s*(C.amplitude κ
q)^2-2*C.leftFilter hκ s q-(C.leftFilter hκ s q)^2)/C.speed κ q) q`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def leftFilter (s q : ℝ) : ℝ :=
  nonlinear s (C.comparisonDensity hκ) ((C.comparisonSpeed hκ).X q)
/--
Defines `leftLinear` of type `ℝ` by `κ*causal 2 (C.comparisonDensity hκ) ((C.comparisonSpeed
hκ).X q)`.

Use: `«2610.05164v2».Calibration.Data.leftLinear_derivative` uses this definition to establish
the actual derivative at the stated point: `HasDerivAt (C.leftLinear hκ) ((κ*(C.amplitude κ
q)^2-2*C.leftLinear hκ q)/C.speed κ q) q`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def leftLinear (q : ℝ) : ℝ :=
  κ*causal 2 (C.comparisonDensity hκ) ((C.comparisonSpeed hκ).X q)

/--
Membership in the specified domain/enclosure: `C.leftFilter hκ s q ∈ Icc (0:ℝ) (s/κ*q)`.

Use: `«2610.05164v2».Calibration.Data.leftFilter_zero` uses this assertion to establish exact
identity `C.leftFilter hκ s 0=0`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».Filters.nonlinear_le_coordinate` with the arguments shown in the proof.
-/
theorem leftFilter_bounds {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Icc (0:ℝ) 2) :
    C.leftFilter hκ s q ∈ Icc (0:ℝ) (s/κ*q) := by
  have hb := nonlinear_le_coordinate (C.comparisonGround hκ) hs ((C.comparisonSpeed hκ).X q)
  rw [(C.comparisonSpeed hκ).groundParameter_density hκ,
    (C.comparisonSpeed hκ).ground_coordinate hκ (C.comparisonGround hκ),
    (C.comparisonSpeed hκ).q_X hq] at hb
  exact ⟨(nonlinear_bounds ((C.comparisonSpeed hκ).density_integrable hκ)
    ((C.comparisonSpeed hκ).density_nonneg hκ) hs _).1,hb⟩

/--
Membership in the specified domain/enclosure: `C.leftLinear hκ q ∈ Icc (0:ℝ) q`.

Use: `«2610.05164v2».Calibration.Data.leftLinear_zero` uses this assertion to establish exact
identity `C.leftLinear hκ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».Filters.linear_le_coordinate`, `«2610.05164v2».Filters.causal_nonneg` with the
arguments shown in the proof.
-/
theorem leftLinear_bounds {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    C.leftLinear hκ q ∈ Icc (0:ℝ) q := by
  -- Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».Filters.linear_le_coordinate`, `«2610.05164v2».Filters.causal_nonneg` with
  -- the arguments shown in the proof.
  have hb := linear_le_coordinate (C.comparisonGround hκ) ((C.comparisonSpeed hκ).X q)
  change groundParameter _ _*causal 2 _ _ ≤ _ at hb
  rw [(C.comparisonSpeed hκ).groundParameter_density hκ,
    (C.comparisonSpeed hκ).ground_coordinate hκ (C.comparisonGround hκ),
    (C.comparisonSpeed hκ).q_X hq] at hb
  exact ⟨mul_nonneg hκ.le (causal_nonneg
    (Eventually.of_forall ((C.comparisonSpeed hκ).density_nonneg hκ)) _),hb⟩

/--
Exact identity `C.leftFilter hκ s 0=0`.

Use: `«2610.05164v2».Calibration.Data.leftDefect_endpoint_bound` rewrites with this identity to
establish the stated quantitative bound `C.leftDefect hκ s q ≤ C.defectConstant κ s*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftFilter_bounds` with
the arguments shown in the proof.
-/
theorem leftFilter_zero {s : ℝ} (hs : 0 ≤ s) : C.leftFilter hκ s 0=0 := by
  have hb := C.leftFilter_bounds hκ hs (q := 0) (by norm_num)
  simp only [mul_zero] at hb
  exact le_antisymm hb.2 hb.1

/--
Exact identity `C.leftLinear hκ 0=0`.

Use: `«2610.05164v2».Calibration.Data.leftLinearDefect_endpoint_bound` rewrites with this
identity to prove the bound `C.leftLinearDefect hκ q ≤ C.defectConstant
κ 0*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.leftLinear_bounds` with
the arguments shown in the proof.
-/
theorem leftLinear_zero : C.leftLinear hκ 0=0 := by
  have hb := C.leftLinear_bounds hκ (q := 0) (by norm_num)
  exact le_antisymm hb.2 hb.1

/--
The actual derivative at the stated point: `HasDerivAt (C.leftFilter hκ s) ((s*(C.amplitude κ
q)^2-2*C.leftFilter hκ s q-(C.leftFilter hκ s q)^2)/C.speed κ q) q`.

Use: `«2610.05164v2».Calibration.Data.leftDefect_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (C.leftDefect hκ s)
(((1+s/κ)*q^2-2*(1+(s/κ)*q)*C.leftDefect hκ s q+ (s/κ)*(C.leftDefect hκ s q)^2)/C.speed κ q)
q`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_hasDerivAt`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem leftFilter_derivative {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (C.leftFilter hκ s)
      ((s*(C.amplitude κ q)^2-2*C.leftFilter hκ s q-(C.leftFilter hκ s q)^2)/C.speed κ q) q := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_hasDerivAt`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  have h := (nonlinear_hasDerivAt ((C.comparisonSpeed hκ).density_integrable hκ)
    ((C.comparisonSpeed hκ).density_nonneg hκ) (C.comparisonDensity_continuous hκ) hs
    ((C.comparisonSpeed hκ).X q)).comp q (C.comparisonX_derivative hκ hq)
  have hm := C.comparisonDensity_formula hκ ((C.comparisonSpeed hκ).X q)
  rw [(C.comparisonSpeed hκ).q_X ⟨hq.1.le,hq.2.le⟩] at hm
  convert h using 1
  · rfl
  · change (C.comparisonSpeed hκ).density κ ((C.comparisonSpeed hκ).X q)=_ at hm
    rw [hm]
    dsimp only [leftFilter,comparisonDensity]
    simp only [div_eq_mul_inv]

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (C.leftFilter hκ
s) 0 2`.

Use: `«2610.05164v2».Calibration.Data.leftDefect_endpoint_bound` uses this assertion to
establish the stated quantitative bound `C.leftDefect hκ s q ≤ C.defectConstant κ s*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_c1`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem leftFilter_ac {s : ℝ} (hs : 0 ≤ s) :
    AbsolutelyContinuousOnInterval (C.leftFilter hκ s) 0 2 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_c1`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
  -- proof.
  let S := C.comparisonSpeed hκ
  have hC := nonlinear_c1 (S.density_integrable hκ) (S.density_nonneg hκ)
    (C.comparisonDensity_continuous hκ) hs
  obtain ⟨K,hK⟩ := (hC.contDiffOn (s := Icc (S.X 0) (S.X 2))).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval _ (S.X_locallyAC 0 2)
  intro q hq
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hq
  exact ⟨S.X_strictMono.monotoneOn (by norm_num) hq hq.1,
    S.X_strictMono.monotoneOn hq (by norm_num) hq.2⟩

/--
The actual derivative at the stated point: `HasDerivAt (C.leftLinear hκ) ((κ*(C.amplitude κ
q)^2-2*C.leftLinear hκ q)/C.speed κ q) q`.

Use: `«2610.05164v2».Calibration.Data.leftLinearDefect_derivative` uses this derivative formula
to establish the actual derivative at the stated point: `HasDerivAt (C.leftLinearDefect hκ)
((q^2-2*C.leftLinearDefect hκ q)/C.speed κ q) q`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_hasDerivAt`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».Calibration.Data.comparisonDensity_continuous` with the arguments shown in the
proof.
-/
theorem leftLinear_derivative {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (C.leftLinear hκ) ((κ*(C.amplitude κ q)^2-2*C.leftLinear hκ q)/C.speed κ q) q := by
  -- Use the identities/estimates `«2610.05164v2».Filters.causal_hasDerivAt`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».Calibration.Data.comparisonDensity_continuous` with the arguments shown in
  -- the proof.
  have h := ((causal_hasDerivAt ((C.comparisonSpeed hκ).density_integrable hκ)
    (C.comparisonDensity_continuous hκ) (by norm_num : (0:ℝ) ≤ 2)
    ((C.comparisonSpeed hκ).X q)).const_mul κ).comp q (C.comparisonX_derivative hκ hq)
  have hm := C.comparisonDensity_formula hκ ((C.comparisonSpeed hκ).X q)
  rw [(C.comparisonSpeed hκ).q_X ⟨hq.1.le,hq.2.le⟩] at hm
  convert h using 1
  · rfl
  · change (C.comparisonSpeed hκ).density κ ((C.comparisonSpeed hκ).X q)=_ at hm
    rw [hm]
    dsimp only [leftLinear,comparisonDensity]
    simp only [div_eq_mul_inv]
    ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (C.leftLinear
hκ) 0 2`.

Use: `«2610.05164v2».Calibration.Data.leftLinearDefect_endpoint_bound` uses this assertion to
establish the stated quantitative bound `C.leftLinearDefect hκ q ≤ C.defectConstant κ
0*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_c1`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».Calibration.Data.comparisonDensity_continuous` with the arguments shown in the
proof.
-/
theorem leftLinear_ac : AbsolutelyContinuousOnInterval (C.leftLinear hκ) 0 2 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.causal_c1`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».Calibration.Data.comparisonDensity_continuous` with the arguments shown in
  -- the proof.
  let S := C.comparisonSpeed hκ
  have hC := causal_c1 (S.density_integrable hκ) (C.comparisonDensity_continuous hκ)
    (by norm_num : (0:ℝ) ≤ 2)
  obtain ⟨K,hK⟩ := (hC.contDiffOn (s := Icc (S.X 0) (S.X 2))).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact (hK.comp_absolutelyContinuousOnInterval (g := S.X)
    (by
      intro q hq
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hq
      exact ⟨S.X_strictMono.monotoneOn (by norm_num) hq hq.1,
        S.X_strictMono.monotoneOn hq (by norm_num) hq.2⟩) (S.X_locallyAC 0 2)).const_mul κ

end
end «2610.05164v2».Calibration.Data
