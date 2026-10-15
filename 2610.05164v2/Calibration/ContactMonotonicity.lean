import «2610.05164v2».Calibration.ReferenceContact

/-!
Article: 2610.05164v2, Theorem 3.2.
Strict monotonicity of the constructed contact coordinate, including its infinite tail, as required
by Theorem 3.2.
Use: `«2610.05164v2».Calibration.ReferenceData.contact_limit` feeds
`«2610.05164v2».Calibration.ReferenceData.contact_image` (contact image).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.contact_image` — 2610.05164v2, Theorem 3.2;
Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Filters «2610.05164v2».Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
Membership in the specified domain/enclosure: `R.referenceSpeed.q x ∈ Ioo (0:ℝ) 2`.

Use: `«2610.05164v2».Calibration.ReferenceData.contactForcing_positive` uses this assertion to
establish the stated quantitative bound `0 < R.contactForcing hσ x`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_mem`,
`«2610.05164v2».PrescribedSpeed.SpeedData.X_q` with the arguments shown in the proof.
-/
theorem coordinate_interior {x : ℝ}
    (hx : x ∈ Ioo (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    R.referenceSpeed.q x ∈ Ioo (0:ℝ) 2 := by
  -- Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_mem`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.X_q` with the arguments shown in the proof.
  have hq := R.referenceSpeed.q_mem x
  have he := R.referenceSpeed.X_q ⟨hx.1.le,hx.2.le⟩
  refine ⟨lt_of_le_of_ne hq.1 ?_,lt_of_le_of_ne hq.2 ?_⟩
  · intro hz
    rw [← hz] at he
    linarith [hx.1]
  · intro hz
    rw [hz] at he
    linarith [hx.2]

/--
The stated quantitative bound `0 < R.contactForcing hσ x`.

Use: `«2610.05164v2».Calibration.ReferenceData.contactSlope_positive` uses this bound to
establish the stated quantitative bound `0 < R.contactSlope hσ x`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.coordinate_interior`,
`«2610.05164v2».Calibration.ReferenceData.filter_bounds`,
`«2610.05164v2».Calibration.ReferenceData.density_formula` with the arguments shown in the
proof.
-/
theorem contactForcing_positive {x : ℝ}
    (hx : x ∈ Ioo (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    0 < R.contactForcing hσ x := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.coordinate_interior`,
  -- `«2610.05164v2».Calibration.ReferenceData.filter_bounds`,
  -- `«2610.05164v2».Calibration.ReferenceData.density_formula` with the arguments shown in the
  -- proof.
  have hq := R.coordinate_interior hx
  have hf := (R.filter_bounds hσ x).1
  have hd : 0 < R.k*R.density x-Q (R.referenceSpeed.q x) := by
    rw [R.density_formula]
    exact R.speed_positive hq
  have hq0 := hq.1
  exact mul_pos (by positivity) hd

/--
The stated quantitative bound `0 < R.contactSlope hσ x`.

Use: `«2610.05164v2».Calibration.ReferenceData.contact_strictMono` uses this bound to establish
the precise assertion is `StrictMonoOn (R.contact hσ) (Ici (R.referenceSpeed.X 0))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.primitive_c1`,
`«2610.05164v2».Calibration.ReferenceData.contactDamping_continuous`,
`«2610.05164v2».Calibration.ReferenceData.contactForcing_continuous` with the arguments shown
in the proof.
-/
theorem contactSlope_positive {x : ℝ} (hx : R.referenceSpeed.X 0 < x) :
    0 < R.contactSlope hσ x := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.primitive_c1`,
  -- `«2610.05164v2».Calibration.ReferenceData.contactDamping_continuous`,
  -- `«2610.05164v2».Calibration.ReferenceData.contactForcing_continuous` with the arguments
  -- shown in the proof.
  let a := R.referenceSpeed.X 0
  let b := R.referenceSpeed.X 2
  let z := min x b
  let φ := fun t => exp (primitive (R.contactDamping hσ) t)*R.contactForcing hσ t
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous φ := (Real.continuous_exp.comp
    («2610.05164v2».Calibration.primitive_c1 (R.contactDamping_continuous hσ)).continuous).mul
      (R.contactForcing_continuous hσ)
  have hz : a < z := lt_min hx R.referenceSpeed.X_endpoint_order
  have hp : 0 < ∫ t in a..z, φ t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable a z) _ hz
    intro t ht
    exact mul_pos (exp_pos _) (R.contactForcing_positive hσ
      ⟨ht.1,ht.2.trans_le (min_le_right x b)⟩)
  have hn : ∀ t, 0 ≤ φ t := fun t => mul_nonneg (exp_pos _).le (R.contactForcing_nonneg hσ t)
  have hm : (∫ t in a..z, φ t) ≤ ∫ t in a..x, φ t := intervalIntegral.integral_mono_interval le_rfl hz.le (min_le_left x b)
    (Eventually.of_forall hn) (hc.intervalIntegrable a x)
  rw [R.contactSlope_integral hσ]
  exact mul_pos (exp_pos _) (hp.trans_le hm)

/--
Continuity of the displayed function: `Continuous (R.contact hσ)`.

Use: `«2610.05164v2».Calibration.ReferenceData.contact_strictMono` uses this continuity result
to establish `StrictMonoOn (R.contact hσ) (Ici (R.referenceSpeed.X
0))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_continuous`,
`«2610.05164v2».Calibration.ReferenceData.filter_c1` with the arguments shown in the proof.
-/
theorem contact_continuous : Continuous (R.contact hσ) :=
  R.referenceSpeed.q_continuous.sub (R.filter_c1 hσ).continuous

/--
The precise assertion is `StrictMonoOn (R.contact hσ) (Ici (R.referenceSpeed.X 0))`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_global_strict_minimum` uses this
assertion to prove the bound `(R.calibration hσ hb hω).F q (R.contact
hσ (R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.contact_continuous`,
`«2610.05164v2».Calibration.ReferenceData.contact_derivative`,
`«2610.05164v2».Calibration.ReferenceData.contactSlope_positive` with the arguments shown in
the proof.
-/
theorem contact_strictMono : StrictMonoOn (R.contact hσ) (Ici (R.referenceSpeed.X 0)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (R.contact_continuous hσ).continuousOn
  intro x hx
  rw [(R.contact_derivative hσ x).deriv]
  exact R.contactSlope_positive hσ (by simpa only [interior_Ici,mem_Ioi] using hx)

/--
Exact identity `R.contact hσ (R.referenceSpeed.X 0)=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.J_contact_integral` rewrites with this identity
to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.filter_zero_left`,
`«2610.05164v2».PrescribedSpeed.SpeedData.q_X` with the arguments shown in the proof.
-/
theorem contact_left : R.contact hσ (R.referenceSpeed.X 0)=0 := by rw [contact,R.filter_zero_left hσ le_rfl,R.referenceSpeed.q_X (by norm_num),sub_zero]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (R.contact hσ)
atTop (𝓝 2)`.

Use: `«2610.05164v2».Calibration.ReferenceData.contact_image` uses this limit to establish
exact identity `R.contact hσ '' Ici (R.referenceSpeed.X 0)=Ico (0:ℝ) 2`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.q_two_right`,
`«2610.05164v2».Filters.nonlinear_limits`,
`«2610.05164v2».Calibration.ReferenceData.density_properties` with the arguments shown in the
proof.
-/
theorem contact_limit : Tendsto (R.contact hσ) atTop (𝓝 2) := by
  -- Record the convergence hq with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hq : Tendsto R.referenceSpeed.q atTop (𝓝 2) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2)).congr'
      ((eventually_ge_atTop (R.referenceSpeed.X 2)).mono (fun _ hx => (R.referenceSpeed.q_two_right hx).symm))
  -- Record the convergence hf with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hf : Tendsto (R.filter hσ) atTop (𝓝 0) := by
    change Tendsto (fun x => nonlinear (σ*R.k) R.density x/σ) atTop (𝓝 0)
    simpa only [zero_div] using ((nonlinear_limits R.density_properties.1 R.density_properties.2.1
      (mul_nonneg hσ.le R.k_positive.le)).2.div_const σ)
  change Tendsto (fun x => R.referenceSpeed.q x-R.filter hσ x) atTop (𝓝 2)
  simpa only [sub_zero] using hq.sub hf

end
end «2610.05164v2».Calibration.ReferenceData
