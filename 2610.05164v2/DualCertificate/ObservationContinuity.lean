import «2610.05164v2».DualCertificate.ReflectedFilters
import «2610.05164v2».DualCertificate.ComparisonContinuity
import «2610.05164v2».Calculus.PositiveParameterIntegral
import «2610.05164v2».Comparison.SymmetricSupport
import «2610.05164v2».Filters.LinearEnergy

/-!
Article: 2610.05164v2, Theorem 3.6.
Actual comparison determinant and trace observations as regular compact integrals.
Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.S_actual` feeds
`«2610.05164v2».DualCertificate.Data.comparisonS_continuous` (comparison S continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` — 2610.05164v2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace «2610.05164v2».DualCertificate.NormalizedCalibration
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Calibration «2610.05164v2».Calculus «2610.05164v2».Filters «2610.05164v2».Continuum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (N : «2610.05164v2».DualCertificate.NormalizedCalibration)

/--
Defines `H` of type `ℝ` by `2*(∫ t in Icc (0:ℝ) 1,N.filter hκ s t*N.velocity κ t)+log
(1+N.filter hκ s 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.H_actual` uses this definition to
establish exact identity `N.H hκ s=logDeterminant (kernelEigenvalue
((N.calibration.comparisonSpeed hκ).density_integrable hκ) ((N.calibration.comparisonSpeed
hκ).density_nonneg hκ)) s`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def H {κ : ℝ} (hκ : 0<κ) (s : ℝ) : ℝ :=
  2*(∫ t in Icc (0:ℝ) 1,N.filter hκ s t*N.velocity κ t)+log (1+N.filter hκ s 1)

/--
Defines `S` of type `ℝ` by `2*(∫ t in Icc (0:ℝ) 1,(N.linear hκ t)^2*N.velocity κ t)+(N.linear
hκ 1)^2`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.S_actual` uses this definition to
establish exact identity `N.S hκ=∫ x,(«2610.05164v2».Filters.linear
((N.calibration.comparisonSpeed hκ).density_integrable hκ) ((N.calibration.comparisonSpeed
hκ).density_nonneg hκ) x)^2`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def S {κ : ℝ} (hκ : 0<κ) : ℝ :=
  2*(∫ t in Icc (0:ℝ) 1,(N.linear hκ t)^2*N.velocity κ t)+(N.linear hκ 1)^2

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.filter
p.1.property s p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.H_continuous` uses this continuity
result to establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => N.H
κ.property s)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.leftFilter_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.cubeMap_continuous` with the arguments
shown in the proof.
-/
theorem filter_joint_continuous {s : ℝ} (hs : 0≤s) :
    Continuous (fun p : ParameterDomain => N.filter p.1.property s p.2) := by convert! (N.calibration.leftFilter_joint_continuous hs).comp cubeMap_continuous using 1

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.linear
p.1.property p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.S_continuous` uses this continuity
result to establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => N.S
κ.property)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.Data.leftLinear_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.cubeMap_continuous` with the arguments
shown in the proof.
-/
theorem linear_joint_continuous :
    Continuous (fun p : ParameterDomain => N.linear p.1.property p.2) := by convert! N.calibration.leftLinear_joint_continuous.comp cubeMap_continuous using 1

/--
Continuity of the displayed function: `Continuous (fun p : ParameterDomain => N.velocity p.1
p.2)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.H_continuous` uses this continuity
result to establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => N.H
κ.property s)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_positive` with the arguments shown
in the proof.
-/
theorem velocity_joint_continuous :
    Continuous (fun p : ParameterDomain => N.velocity p.1 p.2) := by
  have hm : Continuous (fun p : ParameterDomain => ((p.1:ℝ),(p.2:ℝ))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hd := N.speed_smooth.continuousOn.comp_continuous hm (fun p => ⟨p.1.property,p.2.property⟩)
  exact continuous_const.div hd (fun p => (N.speed_positive p.1.property p.2.property).ne')

 /--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => N.H κ.property s)`.

Use: `«2610.05164v2».DualCertificate.Data.comparisonH_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) =>
D.analytic.comparisonH κ.property s)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.positive_parameter_integral_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.filter_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_joint_continuous` with the
arguments shown in the proof.
-/
theorem H_continuous {s : ℝ} (hs : 0≤s) :
    Continuous (fun κ : Ioi (0:ℝ) => N.H κ.property s) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calculus.positive_parameter_integral_continuous`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.filter_joint_continuous`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_joint_continuous` with the
  -- arguments shown in the proof.
  have hi := positive_parameter_integral_continuous
    (fun κ t => N.filter κ.property s t*N.velocity κ t)
    ((N.filter_joint_continuous hs).mul N.velocity_joint_continuous)
  -- Establish continuity hf before using the function at limits or in calculus arguments.
  have hf : Continuous (fun κ : Ioi (0:ℝ) => N.filter κ.property s 1) :=
    (N.filter_joint_continuous hs).comp (f := fun κ : Ioi (0:ℝ) => (κ,(⟨1,by norm_num⟩ : Icc (0:ℝ) 1))) (continuous_id.prodMk (continuous_const (y := (⟨1,by norm_num⟩ : Icc (0:ℝ) 1))))
  apply (continuous_const.mul hi).add
  apply (continuous_const.add hf).log
  intro κ
  have hb := N.calibration.leftFilter_bounds κ.property hs (by norm_num : (1:ℝ)^3∈Icc 0 2)
  exact ne_of_gt (by change 0<1+N.calibration.leftFilter κ.property s ((1:ℝ)^3);linarith [hb.1])

 /--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => N.S κ.property)`.

Use: `«2610.05164v2».DualCertificate.Data.comparisonS_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) =>
D.analytic.comparisonS κ.property)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.positive_parameter_integral_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.linear_joint_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.velocity_joint_continuous` with the
arguments shown in the proof.
-/
theorem S_continuous : Continuous (fun κ : Ioi (0:ℝ) => N.S κ.property) := by
  have hi := positive_parameter_integral_continuous
    (fun κ t => (N.linear κ.property t)^2*N.velocity κ t)
    (N.linear_joint_continuous.pow 2 |>.mul N.velocity_joint_continuous)
  have hf : Continuous (fun κ : Ioi (0:ℝ) => N.linear κ.property 1) :=
    N.linear_joint_continuous.comp (f := fun κ : Ioi (0:ℝ) => (κ,(⟨1,by norm_num⟩ : Icc (0:ℝ) 1))) (continuous_id.prodMk (continuous_const (y := (⟨1,by norm_num⟩ : Icc (0:ℝ) 1))))
  exact (continuous_const.mul hi).add (hf.pow 2)

 /--
The precise assertion is `(∫ x in (N.calibration.comparisonSpeed hκ).X 0..0, f x)= ∫ t in Icc
(0:ℝ) 1,f (N.X hκ t)*N.velocity κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.S_actual` rewrites with this
identity to establish the identity `N.S hκ=∫ x,(«2610.05164v2».Filters.linear
((N.calibration.comparisonSpeed hκ).density_integrable hκ) ((N.calibration.comparisonSpeed
hκ).density_nonneg hκ) x)^2`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.X_continuous`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.X_derivative`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_positive` with the arguments shown
in the proof.
-/
theorem compact_integral {κ : ℝ} (hκ : 0<κ) (f : ℝ → ℝ) :
    (∫ x in (N.calibration.comparisonSpeed hκ).X 0..0,
      f x)=
    ∫ t in Icc (0:ℝ) 1,f (N.X hκ t)*N.velocity κ t := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.X_continuous`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.X_derivative`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.speed_positive` with the arguments
  -- shown in the proof.
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := N.X hκ) (f' := N.velocity κ) (g := f)
    (a := 0) (b := 1) (N.X_continuous hκ).continuousOn
    (fun t ht => N.X_derivative hκ (by simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using ht))
    (fun t ht => div_nonneg (by norm_num : (0:ℝ)≤3) (N.speed_positive hκ
      (by simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using (show t∈Icc (min (0:ℝ) 1) (max (0:ℝ) 1) from ⟨ht.1.le,ht.2.le⟩))).le)
  have hzero : N.X hκ 0=(N.calibration.comparisonSpeed hκ).X 0 := by simp [X]
  have hone : N.X hκ 1=0 := by simp [X,«2610.05164v2».PrescribedSpeed.SpeedData.X]
  rw [hzero,hone] at h
  rw [← h,intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
  rfl

 /--
The precise assertion is `(∫ x in (N.calibration.comparisonSpeed hκ).X 0..0, nonlinear s
(N.calibration.comparisonDensity hκ) x)= ∫ t in Icc (0:ℝ) 1,N.filter hκ s t*N.velocity κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.H_actual` rewrites with this
identity to establish the identity `N.H hκ s=logDeterminant (kernelEigenvalue
((N.calibration.comparisonSpeed hκ).density_integrable hκ) ((N.calibration.comparisonSpeed
hκ).density_nonneg hκ)) s`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.compact_integral` with the arguments
shown in the proof.
-/
theorem compact_filter_integral {κ : ℝ} (hκ : 0<κ) (s : ℝ) :
    (∫ x in (N.calibration.comparisonSpeed hκ).X 0..0,
      nonlinear s (N.calibration.comparisonDensity hκ) x)=
    ∫ t in Icc (0:ℝ) 1,N.filter hκ s t*N.velocity κ t :=
  N.compact_integral hκ (nonlinear s (N.calibration.comparisonDensity hκ))

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
Exact identity `N.H hκ s=logDeterminant (kernelEigenvalue ((N.calibration.comparisonSpeed
hκ).density_integrable hκ) ((N.calibration.comparisonSpeed hκ).density_nonneg hκ)) s`.

Use: `«2610.05164v2».DualCertificate.Data.comparisonH_continuous` uses this identity to
establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) =>
D.analytic.comparisonH κ.property s)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown in the
proof.
-/
theorem H_actual {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s) :
    N.H hκ s=logDeterminant (kernelEigenvalue
      ((N.calibration.comparisonSpeed hκ).density_integrable hκ)
      ((N.calibration.comparisonSpeed hκ).density_nonneg hκ)) s := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown
  -- in the proof.
  let C := N.calibration
  have hz : ∀ x≤(C.comparisonSpeed hκ).X 0,C.comparisonDensity hκ x=0 := by
    intro x hx
    exact (C.comparisonSpeed hκ).density_zero_outside κ (fun h => (not_lt_of_ge hx) h.1)
  rw [«2610.05164v2».Comparison.symmetric_logDeterminant_support
    ((C.comparisonSpeed hκ).density_integrable hκ) ((C.comparisonSpeed hκ).density_nonneg hκ)
    (C.comparisonDensity_continuous hκ) (C.comparisonDensity_reflection hκ hΓ) hs _ hz]
  change N.H hκ s=2*(∫ x in (N.calibration.comparisonSpeed hκ).X 0..0,
    nonlinear s (N.calibration.comparisonDensity hκ) x)+log (1+nonlinear s (N.calibration.comparisonDensity hκ) 0)
  rw [N.compact_filter_integral hκ]
  unfold H filter «2610.05164v2».Calibration.Data.leftFilter
  simp [«2610.05164v2».PrescribedSpeed.SpeedData.X]

include hΓ in
/--
Exact identity `N.S hκ=∫ x,(«2610.05164v2».Filters.linear ((N.calibration.comparisonSpeed
hκ).density_integrable hκ) ((N.calibration.comparisonSpeed hκ).density_nonneg hκ) x)^2`.

Use: `«2610.05164v2».DualCertificate.Data.comparisonS_continuous` uses this identity to
establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) =>
D.analytic.comparisonS κ.property)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown in the
proof.
-/
theorem S_actual {κ : ℝ} (hκ : 0<κ) :
    N.S hκ=∫ x,(«2610.05164v2».Filters.linear
      ((N.calibration.comparisonSpeed hκ).density_integrable hκ)
      ((N.calibration.comparisonSpeed hκ).density_nonneg hκ) x)^2 := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown
  -- in the proof.
  let C := N.calibration
  let hm := (C.comparisonSpeed hκ).density_integrable hκ
  let hn := (C.comparisonSpeed hκ).density_nonneg hκ
  have hz : ∀ x≤(C.comparisonSpeed hκ).X 0,C.comparisonDensity hκ x=0 := by
    intro x hx
    exact (C.comparisonSpeed hκ).density_zero_outside κ (fun h => (not_lt_of_ge hx) h.1)
  rw [linear_square_trace hm hn,«2610.05164v2».Comparison.symmetric_square_trace_support hm hn
    (C.comparisonDensity_continuous hκ) (C.comparisonDensity_reflection hκ hΓ) _ hz]
  change N.S hκ=2*(∫ x in (N.calibration.comparisonSpeed hκ).X 0..0,(«2610.05164v2».Filters.linear hm hn x)^2)+
    («2610.05164v2».Filters.linear hm hn 0)^2
  rw [N.compact_integral hκ (fun x => («2610.05164v2».Filters.linear hm hn x)^2)]
  have hk := (C.comparisonSpeed hκ).groundParameter_density hκ
  unfold S linear «2610.05164v2».Calibration.Data.leftLinear «2610.05164v2».Filters.linear
  rw [hk]
  have hx : (C.comparisonSpeed hκ).X ((1:ℝ)^3)=0 := by simp [«2610.05164v2».PrescribedSpeed.SpeedData.X]
  rw [hx]
  rfl

end
end «2610.05164v2».DualCertificate.NormalizedCalibration
