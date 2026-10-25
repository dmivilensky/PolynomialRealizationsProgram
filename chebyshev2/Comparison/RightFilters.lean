import chebyshev2.Comparison.Regularity
import chebyshev2.Comparison.GroundReflection

/-!
Article: chebyshev2, Lemma 11.
Definition 6 and Lemma 11: right filters of the actual comparison density, including classical
interior equations and absolute continuity at both endpoints.
Use: `chebyshev2.Calibration.Data.comparisonX_derivative` feeds
`chebyshev2.Calibration.Data.rightFilter_derivative` (right Filter derivative).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.GroundState chebyshev2.Filters chebyshev2.Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)

/--
Defines `comparisonGround` of type `GroundWitness ((C.comparisonSpeed hκ).density_integrable
hκ) ((C.comparisonSpeed hκ).density_nonneg hκ)` by `Classical.choice (ground_state _ _
((C.comparisonSpeed hκ).density_nonzero hκ))`.

Use: `chebyshev2.Calibration.Data.rightFilter_bounds` uses this definition to establish
membership in the specified domain/enclosure: `C.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonGround : GroundWitness ((C.comparisonSpeed hκ).density_integrable hκ)
    ((C.comparisonSpeed hκ).density_nonneg hκ) :=
  Classical.choice (ground_state _ _ ((C.comparisonSpeed hκ).density_nonzero hκ))

/--
Constructs the object of type `GroundWitness (reflected_integrable ((C.comparisonSpeed
hκ).density_integrable hκ)) (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ))` and
discharges its required properties in the accompanying proof.

Use: `chebyshev2.Calibration.Data.rightFilter_bounds` uses this definition to establish
membership in the specified domain/enclosure: `C.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
def reflectedComparisonGround : GroundWitness
    (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  apply Classical.choice (ground_state _ _ ?_)
  intro he
  have hz := integral_congr_ae he
  simp only [Pi.zero_apply,integral_zero] at hz
  have hp := (C.comparisonGround hκ).mass_positive
  change (∫ x, (C.comparisonSpeed hκ).density κ (-x))=0 at hz
  rw [integral_neg_eq_self] at hz
  linarith

/--
Defines `rightFilter` of type `ℝ` by `nonlinear s (reflected (C.comparisonDensity hκ))
(-((C.comparisonSpeed hκ).X q))`.

Use: `chebyshev2.Calibration.Data.rightFilter_derivative` uses this definition to establish
the actual derivative at the stated point: `HasDerivAt (C.rightFilter hκ s) ((-s*(C.amplitude κ
q)^2+2*C.rightFilter hκ s q+(C.rightFilter hκ s q)^2)/C.speed κ q) q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def rightFilter (s q : ℝ) : ℝ :=
  nonlinear s (reflected (C.comparisonDensity hκ)) (-((C.comparisonSpeed hκ).X q))
/--
Defines `rightLinear` of type `ℝ` by `κ*causal 2 (reflected (C.comparisonDensity hκ))
(-((C.comparisonSpeed hκ).X q))`.

Use: `chebyshev2.Calibration.Data.rightLinear_derivative` uses this definition to establish
the actual derivative at the stated point: `HasDerivAt (C.rightLinear hκ) ((-κ*(C.amplitude κ
q)^2+2*C.rightLinear hκ q)/C.speed κ q) q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def rightLinear (q : ℝ) : ℝ :=
  κ*causal 2 (reflected (C.comparisonDensity hκ)) (-((C.comparisonSpeed hκ).X q))

/--
Membership in the specified domain/enclosure: `C.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q))`.

Use: `chebyshev2.Calibration.Data.rightFilter_two` uses this assertion to establish exact
identity `C.rightFilter hκ s 2=0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.Filters.reflected_integrable` with the arguments shown in the proof.
-/
theorem rightFilter_bounds {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Icc (0:ℝ) 2) :
    C.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q)) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
  -- `chebyshev2.Filters.reflected_integrable` with the arguments shown in the proof.
  let G := C.comparisonGround hκ
  let Gr := C.reflectedComparisonGround hκ
  have hc := C.comparisonDensity_continuous hκ
  have hp : groundParameter (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
      (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ))=κ :=
    (groundParameter_reflection G hc).trans ((C.comparisonSpeed hκ).groundParameter_density hκ)
  have hqv : Gr.q (-((C.comparisonSpeed hκ).X q))=2-q := by
    rw [groundCoordinate_reflection G hc Gr,neg_neg,(C.comparisonSpeed hκ).ground_coordinate hκ G,
      (C.comparisonSpeed hκ).q_X hq]
  constructor
  · exact (nonlinear_bounds (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
      (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)) hs _).1
  · have hb := nonlinear_le_coordinate Gr hs (-((C.comparisonSpeed hκ).X q))
    rw [hp,hqv] at hb
    exact hb

/--
Membership in the specified domain/enclosure: `C.rightLinear hκ q ∈ Icc (0:ℝ) (2-q)`.

Use: `chebyshev2.Calibration.Data.rightLinear_two` uses this assertion to establish exact
identity `C.rightLinear hκ 2=0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.Filters.reflected_integrable` with the arguments shown in the proof.
-/
theorem rightLinear_bounds {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    C.rightLinear hκ q ∈ Icc (0:ℝ) (2-q) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
  -- `chebyshev2.Filters.reflected_integrable` with the arguments shown in the proof.
  let G := C.comparisonGround hκ
  let Gr := C.reflectedComparisonGround hκ
  have hc := C.comparisonDensity_continuous hκ
  have hp : groundParameter (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
      (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ))=κ :=
    (groundParameter_reflection G hc).trans ((C.comparisonSpeed hκ).groundParameter_density hκ)
  constructor
  · exact mul_nonneg hκ.le (causal_nonneg (Eventually.of_forall
      (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ))) _)
  · have hb := linear_le_coordinate Gr (-((C.comparisonSpeed hκ).X q))
    change groundParameter _ _*causal 2 _ _ ≤ Gr.q _ at hb
    rw [hp,groundCoordinate_reflection G hc Gr,neg_neg,
      (C.comparisonSpeed hκ).ground_coordinate hκ G,(C.comparisonSpeed hκ).q_X hq] at hb
    exact hb

/--
Exact identity `C.rightFilter hκ s 2=0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.rightFilter_bounds` with
the arguments shown in the proof.
-/
theorem rightFilter_two {s : ℝ} (hs : 0 ≤ s) : C.rightFilter hκ s 2=0 := by
  have hb := C.rightFilter_bounds hκ hs (q := 2) (by norm_num)
  simp only [sub_self,mul_zero] at hb
  exact le_antisymm hb.2 hb.1

/--
Exact identity `C.rightLinear hκ 2=0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.rightLinear_bounds` with
the arguments shown in the proof.
-/
theorem rightLinear_two : C.rightLinear hκ 2=0 := by
  have hb := C.rightLinear_bounds hκ (q := 2) (by norm_num)
  simp only [sub_self] at hb
  exact le_antisymm hb.2 hb.1

/--
The actual derivative at the stated point: `HasDerivAt (C.comparisonSpeed hκ).X (C.speed κ q)⁻¹
q`.

Use: `chebyshev2.Calibration.Data.rightFilter_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (C.rightFilter hκ s)
((-s*(C.amplitude κ q)^2+2*C.rightFilter hκ s q+(C.rightFilter hκ s q)^2)/C.speed κ q) q`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem comparisonX_derivative {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (C.comparisonSpeed hκ).X (C.speed κ q)⁻¹ q := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  let S := C.comparisonSpeed hκ
  -- Establish continuity hcD before using the function at limits or in calculus arguments.
  have hcD : ContinuousAt (C.speed κ) q := by
    exact (((C.amplitude_continuousOn_fixed hκ).continuousAt
      (Icc_mem_nhds hq.1 hq.2)).pow 2 |>.const_mul κ).sub
      ((by unfold chebyshev2.Calibration.Q; fun_prop : Continuous (fun t : ℝ => chebyshev2.Calibration.Q t)).continuousAt)
  -- Establish continuity hcr before using the function at limits or in calculus arguments.
  have hcr : ContinuousAt S.reciprocal q := by
    apply (hcD.inv₀ (C.speed_positive hκ hq).ne').congr
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
    exact (indicator_of_mem ht (fun q => (S.D q)⁻¹)).symm
  have hm : Measurable S.reciprocal := S.measurable.inv.indicator measurableSet_Ioo
  have h := intervalIntegral.integral_hasDerivAt_right (a := 1) (b := q) S.reciprocal_integrable_global.intervalIntegrable
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hcr
  change HasDerivAt S.X (S.reciprocal q) q at h
  rw [SpeedData.reciprocal,indicator_of_mem hq] at h
  change HasDerivAt (C.comparisonSpeed hκ).X (C.speed κ q)⁻¹ q at h
  exact h

/--
The actual derivative at the stated point: `HasDerivAt (C.rightFilter hκ s) ((-s*(C.amplitude κ
q)^2+2*C.rightFilter hκ s q+(C.rightFilter hκ s q)^2)/C.speed κ q) q`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_hasDerivAt`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightFilter_derivative {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (C.rightFilter hκ s)
      ((-s*(C.amplitude κ q)^2+2*C.rightFilter hκ s q+(C.rightFilter hκ s q)^2)/C.speed κ q) q := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_hasDerivAt`,
  -- `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := (nonlinear_hasDerivAt
    (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ))
    (reflected_continuous (C.comparisonDensity_continuous hκ)) hs
    (-((C.comparisonSpeed hκ).X q))).comp q (C.comparisonX_derivative hκ hq).neg
  have hm : reflected (C.comparisonDensity hκ) (-((C.comparisonSpeed hκ).X q))=
      (C.amplitude κ q)^2 := by
    rw [reflected,neg_neg,C.comparisonDensity_formula hκ,(C.comparisonSpeed hκ).q_X ⟨hq.1.le,hq.2.le⟩]
  convert h using 1
  · rfl
  · change reflected ((C.comparisonSpeed hκ).density κ) (-((C.comparisonSpeed hκ).X q))=_ at hm
    rw [hm]
    dsimp only [rightFilter,comparisonDensity]
    simp only [div_eq_mul_inv]
    ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (C.rightFilter
hκ s) 0 2`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_c1`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightFilter_ac {s : ℝ} (hs : 0 ≤ s) :
    AbsolutelyContinuousOnInterval (C.rightFilter hκ s) 0 2 := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_c1`,
  -- `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  let S := C.comparisonSpeed hκ
  have hC := nonlinear_c1 (reflected_integrable (S.density_integrable hκ))
    (reflected_nonneg (S.density_nonneg hκ))
    (reflected_continuous (C.comparisonDensity_continuous hκ)) hs
  obtain ⟨K,hK⟩ := (hC.contDiffOn (s := Icc (-S.X 2) (-S.X 0))).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval _ (S.X_locallyAC 0 2).neg
  intro q hq
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hq
  exact ⟨neg_le_neg (S.X_strictMono.monotoneOn hq (by norm_num) hq.2),
    neg_le_neg (S.X_strictMono.monotoneOn (by norm_num) hq hq.1)⟩


/--
The actual derivative at the stated point: `HasDerivAt (C.rightLinear hκ) ((-κ*(C.amplitude κ
q)^2+2*C.rightLinear hκ q)/C.speed κ q) q`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_hasDerivAt`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightLinear_derivative {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (C.rightLinear hκ)
      ((-κ*(C.amplitude κ q)^2+2*C.rightLinear hκ q)/C.speed κ q) q := by
  -- Use the identities/estimates `chebyshev2.Filters.causal_hasDerivAt`,
  -- `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := ((causal_hasDerivAt (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_continuous (C.comparisonDensity_continuous hκ)) (by norm_num : (0:ℝ) ≤ 2)
    (-((C.comparisonSpeed hκ).X q))).const_mul κ).comp q (C.comparisonX_derivative hκ hq).neg
  have hm : reflected ((C.comparisonSpeed hκ).density κ) (-((C.comparisonSpeed hκ).X q))=
      (C.amplitude κ q)^2 := by
    change reflected (C.comparisonDensity hκ) (-((C.comparisonSpeed hκ).X q))=_
    rw [reflected,neg_neg,C.comparisonDensity_formula hκ,(C.comparisonSpeed hκ).q_X ⟨hq.1.le,hq.2.le⟩]
  convert h using 1
  · rfl
  · rw [hm]
    dsimp only [rightLinear,comparisonDensity]
    simp only [div_eq_mul_inv]
    ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (C.rightLinear
hκ) 0 2`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightLinear_ac : AbsolutelyContinuousOnInterval (C.rightLinear hκ) 0 2 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let S := C.comparisonSpeed hκ
  let mr := reflected (C.comparisonDensity hκ)
  have hm := reflected_integrable (S.density_integrable hκ)
  have hc := reflected_continuous (C.comparisonDensity_continuous hκ)
  have hC : ContDiff ℝ 1 (causal 2 mr) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (causal_hasDerivAt hm hc (by norm_num : (0:ℝ) ≤ 2) x).differentiableAt,?_⟩
    have he : deriv (causal 2 mr)=fun x => mr x-2*causal 2 mr x :=
      funext (fun x => (causal_hasDerivAt hm hc (by norm_num : (0:ℝ) ≤ 2) x).deriv)
    rw [he]
    exact hc.sub (continuous_const.mul (causal_continuous (by norm_num : (0:ℝ) ≤ 2) hm))
  obtain ⟨K,hK⟩ := (hC.contDiffOn (s := Icc (-S.X 2) (-S.X 0))).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hac := hK.comp_absolutelyContinuousOnInterval (g := fun q => -S.X q)
    (a := 0) (b := 2) (by
      intro q hq
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hq
      exact ⟨neg_le_neg (S.X_strictMono.monotoneOn hq (by norm_num) hq.2),
        neg_le_neg (S.X_strictMono.monotoneOn (by norm_num) hq hq.1)⟩) (S.X_locallyAC 0 2).neg
  exact hac.const_mul κ

end
end chebyshev2.Calibration.Data
