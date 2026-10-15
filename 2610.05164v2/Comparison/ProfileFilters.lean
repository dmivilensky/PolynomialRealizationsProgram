import «2610.05164v2».Comparison.ProfileGeometry

/-!
Article: 2610.05164v2, Theorem 3.4.
Definition 6 and Lemma 11: right filters of the actual comparison density, including classical
interior equations and absolute continuity at both endpoints.
Use: `«2610.05164v2».Comparison.Profile.rightLinear_derivative` feeds
`«2610.05164v2».Comparison.Profile.tracePotential_fderiv` (trace Potential fderiv).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_trace_comparison` — 2610.05164v2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».PrescribedSpeed «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : «2610.05164v2».Comparison.Profile κ) (hκ : 0 < κ)

/--
Defines `ground` of type `GroundWitness ((P.speedData hκ).density_integrable hκ) ((P.speedData
hκ).density_nonneg hκ)` by `Classical.choice (ground_state _ _ ((P.speedData
hκ).density_nonzero hκ))`.

Use: `«2610.05164v2».Comparison.Profile.rightFilter_bounds` uses this definition to establish
membership in the specified domain/enclosure: `P.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def ground : GroundWitness ((P.speedData hκ).density_integrable hκ)
    ((P.speedData hκ).density_nonneg hκ) :=
  Classical.choice (ground_state _ _ ((P.speedData hκ).density_nonzero hκ))

/--
Constructs the object of type `GroundWitness (reflected_integrable ((P.speedData
hκ).density_integrable hκ)) (reflected_nonneg ((P.speedData hκ).density_nonneg hκ))` and
discharges its required properties in the accompanying proof.

Use: `«2610.05164v2».Comparison.Profile.rightFilter_bounds` uses this definition to establish
membership in the specified domain/enclosure: `P.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
def reflectedComparisonGround : GroundWitness
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  apply Classical.choice (ground_state _ _ ?_)
  intro he
  have hz := integral_congr_ae he
  simp only [Pi.zero_apply,integral_zero] at hz
  have hp := (P.ground hκ).mass_positive
  change (∫ x, (P.speedData hκ).density κ (-x))=0 at hz
  rw [integral_neg_eq_self] at hz
  linarith

/--
Defines `rightFilter` of type `ℝ` by `nonlinear s (reflected (P.density hκ)) (-((P.speedData
hκ).X q))`.

Use: `«2610.05164v2».Comparison.Profile.rightFilter_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt (P.rightFilter hκ s)
((-s*(P.amplitude q)^2+2*P.rightFilter hκ s q+(P.rightFilter hκ s q)^2)/P.speed q) q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def rightFilter (s q : ℝ) : ℝ :=
  nonlinear s (reflected (P.density hκ)) (-((P.speedData hκ).X q))
/--
Defines `rightLinear` of type `ℝ` by `κ*causal 2 (reflected (P.density hκ)) (-((P.speedData
hκ).X q))`.

Use: `«2610.05164v2».Comparison.Profile.rightLinear_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt (P.rightLinear hκ)
((-κ*(P.amplitude q)^2+2*P.rightLinear hκ q)/P.speed q) q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def rightLinear (q : ℝ) : ℝ :=
  κ*causal 2 (reflected (P.density hκ)) (-((P.speedData hκ).X q))

/--
Membership in the specified domain/enclosure: `P.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q))`.

Use: `«2610.05164v2».Comparison.Profile.rightFilter_two` uses this assertion to establish exact
identity `P.rightFilter hκ s 2=0`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».Filters.reflected_integrable` with the arguments shown in the proof.
-/
theorem rightFilter_bounds {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Icc (0:ℝ) 2) :
    P.rightFilter hκ s q ∈ Icc (0:ℝ) (s/κ*(2-q)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».Filters.reflected_integrable` with the arguments shown in the proof.
  let G := P.ground hκ
  let Gr := P.reflectedComparisonGround hκ
  have hc := P.density_continuous hκ
  have hp : groundParameter (reflected_integrable ((P.speedData hκ).density_integrable hκ))
      (reflected_nonneg ((P.speedData hκ).density_nonneg hκ))=κ :=
    (groundParameter_reflection G hc).trans ((P.speedData hκ).groundParameter_density hκ)
  have hqv : Gr.q (-((P.speedData hκ).X q))=2-q := by
    rw [groundCoordinate_reflection G hc Gr,neg_neg,(P.speedData hκ).ground_coordinate hκ G,
      (P.speedData hκ).q_X hq]
  constructor
  · exact (nonlinear_bounds (reflected_integrable ((P.speedData hκ).density_integrable hκ))
      (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs _).1
  · have hb := nonlinear_le_coordinate Gr hs (-((P.speedData hκ).X q))
    rw [hp,hqv] at hb
    exact hb

/--
Membership in the specified domain/enclosure: `P.rightLinear hκ q ∈ Icc (0:ℝ) (2-q)`.

Use: `«2610.05164v2».Comparison.Profile.rightLinear_two` uses this assertion to establish exact
identity `P.rightLinear hκ 2=0`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».Filters.reflected_integrable` with the arguments shown in the proof.
-/
theorem rightLinear_bounds {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    P.rightLinear hκ q ∈ Icc (0:ℝ) (2-q) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».Filters.reflected_integrable` with the arguments shown in the proof.
  let G := P.ground hκ
  let Gr := P.reflectedComparisonGround hκ
  have hc := P.density_continuous hκ
  have hp : groundParameter (reflected_integrable ((P.speedData hκ).density_integrable hκ))
      (reflected_nonneg ((P.speedData hκ).density_nonneg hκ))=κ :=
    (groundParameter_reflection G hc).trans ((P.speedData hκ).groundParameter_density hκ)
  constructor
  · exact mul_nonneg hκ.le (causal_nonneg (Eventually.of_forall
      (reflected_nonneg ((P.speedData hκ).density_nonneg hκ))) _)
  · have hb := linear_le_coordinate Gr (-((P.speedData hκ).X q))
    change groundParameter _ _*causal 2 _ _ ≤ Gr.q _ at hb
    rw [hp,groundCoordinate_reflection G hc Gr,neg_neg,
      (P.speedData hκ).ground_coordinate hκ G,(P.speedData hκ).q_X hq] at hb
    exact hb

/--
Exact identity `P.rightFilter hκ s 2=0`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_two` rewrites with this identity
to establish the identity `P.determinantPotential hκ s 2 r=log (1+r/2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightFilter_bounds` with
the arguments shown in the proof.
-/
theorem rightFilter_two {s : ℝ} (hs : 0 ≤ s) : P.rightFilter hκ s 2=0 := by
  have hb := P.rightFilter_bounds hκ hs (q := 2) (by norm_num)
  simp only [sub_self,mul_zero] at hb
  exact le_antisymm hb.2 hb.1

/--
Exact identity `P.rightLinear hκ 2=0`.

Use: `«2610.05164v2».Comparison.Profile.tracePotential_two` rewrites with this identity to
establish exact identity `P.tracePotential hκ 2 r=r^2/4`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.rightLinear_bounds` with
the arguments shown in the proof.
-/
theorem rightLinear_two : P.rightLinear hκ 2=0 := by
  have hb := P.rightLinear_bounds hκ (q := 2) (by norm_num)
  simp only [sub_self] at hb
  exact le_antisymm hb.2 hb.1

/--
The actual derivative at the stated point: `HasDerivAt (P.speedData hκ).X (P.speed q)⁻¹ q`.

Use: `«2610.05164v2».Comparison.Profile.rightFilter_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (P.rightFilter hκ s)
((-s*(P.amplitude q)^2+2*P.rightFilter hκ s q+(P.rightFilter hκ s q)^2)/P.speed q) q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem X_derivative {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (P.speedData hκ).X (P.speed q)⁻¹ q := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  let S := P.speedData hκ
  -- Establish continuity hcD before using the function at limits or in calculus arguments.
  have hcD : ContinuousAt (P.speed) q := by
    exact ((P.extendedAmplitude_continuous.pow 2).const_mul κ |>.sub
      (by unfold «2610.05164v2».Calibration.Q; fun_prop)).continuousAt
  -- Establish continuity hcr before using the function at limits or in calculus arguments.
  have hcr : ContinuousAt S.reciprocal q := by
    apply (hcD.inv₀ ((P.speedData hκ).positive q hq).ne').congr
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
    exact (indicator_of_mem ht (fun q => (S.D q)⁻¹)).symm
  have hm : Measurable S.reciprocal := S.measurable.inv.indicator measurableSet_Ioo
  have h := intervalIntegral.integral_hasDerivAt_right (a := 1) (b := q) S.reciprocal_integrable_global.intervalIntegrable
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hcr
  change HasDerivAt S.X (S.reciprocal q) q at h
  rw [SpeedData.reciprocal,indicator_of_mem hq] at h
  change HasDerivAt (P.speedData hκ).X (P.speed q)⁻¹ q at h
  exact h

/--
The actual derivative at the stated point: `HasDerivAt (P.rightFilter hκ s) ((-s*(P.amplitude
q)^2+2*P.rightFilter hκ s q+(P.rightFilter hκ s q)^2)/P.speed q) q`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_fderiv` uses this derivative
formula to establish the Fréchet derivative formula stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_hasDerivAt`,
`«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightFilter_derivative {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (P.rightFilter hκ s)
      ((-s*(P.amplitude q)^2+2*P.rightFilter hκ s q+(P.rightFilter hκ s q)^2)/P.speed q) q := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_hasDerivAt`,
  -- `«2610.05164v2».Filters.reflected_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := (nonlinear_hasDerivAt
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ))
    (reflected_continuous (P.density_continuous hκ)) hs
    (-((P.speedData hκ).X q))).comp q (P.X_derivative hκ hq).neg
  have hm : reflected (P.density hκ) (-((P.speedData hκ).X q))=
      (P.amplitude q)^2 := by
    rw [reflected,neg_neg,P.density_formula hκ,(P.speedData hκ).q_X ⟨hq.1.le,hq.2.le⟩]
  convert h using 1
  · rfl
  · change reflected ((P.speedData hκ).density κ) (-((P.speedData hκ).X q))=_ at hm
    rw [hm]
    dsimp only [rightFilter,density]
    simp only [div_eq_mul_inv]
    ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (P.rightFilter
hκ s) 0 2`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.4.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_c1`,
`«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightFilter_ac {s : ℝ} (hs : 0 ≤ s) :
    AbsolutelyContinuousOnInterval (P.rightFilter hκ s) 0 2 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_c1`,
  -- `«2610.05164v2».Filters.reflected_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  let S := P.speedData hκ
  have hC := nonlinear_c1 (reflected_integrable (S.density_integrable hκ))
    (reflected_nonneg (S.density_nonneg hκ))
    (reflected_continuous (P.density_continuous hκ)) hs
  obtain ⟨K,hK⟩ := (hC.contDiffOn (s := Icc (-S.X 2) (-S.X 0))).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval _ (S.X_locallyAC 0 2).neg
  intro q hq
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at hq
  exact ⟨neg_le_neg (S.X_strictMono.monotoneOn hq (by norm_num) hq.2),
    neg_le_neg (S.X_strictMono.monotoneOn (by norm_num) hq hq.1)⟩


/--
The actual derivative at the stated point: `HasDerivAt (P.rightLinear hκ) ((-κ*(P.amplitude
q)^2+2*P.rightLinear hκ q)/P.speed q) q`.

Use: `«2610.05164v2».Comparison.Profile.tracePotential_fderiv` uses this derivative formula to
establish the actual Fréchet derivative: `HasFDerivAt (fun p : ℝ × ℝ => P.tracePotential hκ p.1
p.2) (P.traceGradientQ hκ p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ+ P.traceGradientR hκ p.1 p.2
• ContinuousLinearMap.snd ℝ ℝ ℝ) p`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_hasDerivAt`,
`«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightLinear_derivative {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (P.rightLinear hκ)
      ((-κ*(P.amplitude q)^2+2*P.rightLinear hκ q)/P.speed q) q := by
  -- Use the identities/estimates `«2610.05164v2».Filters.causal_hasDerivAt`,
  -- `«2610.05164v2».Filters.reflected_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := ((causal_hasDerivAt (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_continuous (P.density_continuous hκ)) (by norm_num : (0:ℝ) ≤ 2)
    (-((P.speedData hκ).X q))).const_mul κ).comp q (P.X_derivative hκ hq).neg
  have hm : reflected ((P.speedData hκ).density κ) (-((P.speedData hκ).X q))=
      (P.amplitude q)^2 := by
    change reflected (P.density hκ) (-((P.speedData hκ).X q))=_
    rw [reflected,neg_neg,P.density_formula hκ,(P.speedData hκ).q_X ⟨hq.1.le,hq.2.le⟩]
  convert h using 1
  · rfl
  · rw [hm]
    dsimp only [rightLinear,density]
    simp only [div_eq_mul_inv]
    ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (P.rightLinear
hκ) 0 2`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.4.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightLinear_ac : AbsolutelyContinuousOnInterval (P.rightLinear hκ) 0 2 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let S := P.speedData hκ
  let mr := reflected (P.density hκ)
  have hm := reflected_integrable (S.density_integrable hκ)
  have hc := reflected_continuous (P.density_continuous hκ)
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
end «2610.05164v2».Comparison.Profile
