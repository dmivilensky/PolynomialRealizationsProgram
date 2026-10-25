import chebyshev2.Calibration.ReferenceDensity
import chebyshev2.Comparison.Variation

/-!
Article: chebyshev2, Theorem 3.2.
The contact coordinate and its scalar differential equation in Appendix D.
Use: `chebyshev2.Calibration.ReferenceData.contactSlope_integral` feeds
`chebyshev2.Calibration.ReferenceData.contactSlope_positive` (contact Slope positive).
Proof chain: `chebyshev2.Calibration.ReferenceData.contact_strictMono` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Filters chebyshev2.Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
Defines `filter` of type `ℝ` by `nonlinear (σ*R.k) R.density x/σ`.

Use: `chebyshev2.Calibration.ReferenceData.contact` uses this definition in the displayed
construction of `contact`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def filter (_hσ : 0 < σ) (x : ℝ) : ℝ := nonlinear (σ*R.k) R.density x/σ
/--
Defines `contact` of type `ℝ` by `R.referenceSpeed.q x-R.filter hσ x`.

Use: `chebyshev2.Calibration.ReferenceData.contact_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt (R.contact hσ) (R.contactSlope
hσ x) x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def contact (x : ℝ) : ℝ := R.referenceSpeed.q x-R.filter hσ x
/--
Defines `contactSlope` of type `ℝ` by `2*R.filter hσ x+σ*(R.filter hσ x)^2-Q
(R.referenceSpeed.q x)`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_continuous` uses this definition to
establish continuity of the displayed function: `Continuous (R.contactSlope hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def contactSlope (x : ℝ) : ℝ :=
  2*R.filter hσ x+σ*(R.filter hσ x)^2-Q (R.referenceSpeed.q x)
/--
Defines `contactDamping` of type `ℝ` by `2+2*σ*R.filter hσ x`.

Use: `chebyshev2.Calibration.ReferenceData.contactDamping_continuous` uses this definition
to establish continuity of the displayed function: `Continuous (R.contactDamping hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def contactDamping (x : ℝ) : ℝ := 2+2*σ*R.filter hσ x
/--
Defines `contactForcing` of type `ℝ` by `(2*R.referenceSpeed.q x+2*σ*R.filter hσ x)*
(R.k*R.density x-Q (R.referenceSpeed.q x))`.

Use: `chebyshev2.Calibration.ReferenceData.contactForcing_continuous` uses this definition
to establish continuity of the displayed function: `Continuous (R.contactForcing hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def contactForcing (x : ℝ) : ℝ :=
  (2*R.referenceSpeed.q x+2*σ*R.filter hσ x)*
    (R.k*R.density x-Q (R.referenceSpeed.q x))

/--
The actual derivative at the stated point: `HasDerivAt (R.filter hσ) (R.k*R.density
x-2*R.filter hσ x-σ*(R.filter hσ x)^2) x`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (R.contactSlope hσ)
(-R.contactDamping hσ x*R.contactSlope hσ x+R.contactForcing hσ x) x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem filter_derivative (x : ℝ) : HasDerivAt (R.filter hσ)
    (R.k*R.density x-2*R.filter hσ x-σ*(R.filter hσ x)^2) x := by
  have hd := (nonlinear_hasDerivAt R.density_properties.1 R.density_properties.2.1 R.density_continuous
    (mul_nonneg hσ.le R.k_positive.le) x).div_const σ
  convert! hd using 1
  dsimp [filter]
  field_simp

/--
Smoothness to the stated order: `ContDiff ℝ 1 (R.filter hσ)`.

Use: `chebyshev2.Calibration.ReferenceData.contactDamping_continuous` uses this assertion
to establish continuity of the displayed function: `Continuous (R.contactDamping hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_c1`,
`chebyshev2.Calibration.ReferenceData.density_properties`,
`chebyshev2.Calibration.ReferenceData.density_continuous` with the arguments shown in the
proof.
-/
theorem filter_c1 : ContDiff ℝ 1 (R.filter hσ) :=
  (nonlinear_c1 R.density_properties.1 R.density_properties.2.1 R.density_continuous
    (mul_nonneg hσ.le R.k_positive.le)).div_const σ

/--
Membership in the specified domain/enclosure: `R.filter hσ x ∈ Icc (0:ℝ) (R.referenceSpeed.q
x)`.

Use: `chebyshev2.Calibration.ReferenceData.contactForcing_nonneg` uses this assertion to
establish the stated quantitative bound `0 ≤ R.contactForcing hσ x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_le_coordinate`,
`chebyshev2.Filters.nonlinear_bounds`,
`chebyshev2.Calibration.ReferenceData.density_properties` with the arguments shown in the
proof.
-/
theorem filter_bounds (x : ℝ) : R.filter hσ x ∈ Icc (0:ℝ) (R.referenceSpeed.q x) := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_le_coordinate`,
  -- `chebyshev2.Filters.nonlinear_bounds`,
  -- `chebyshev2.Calibration.ReferenceData.density_properties` with the arguments shown in
  -- the proof.
  let G := R.profile.ground R.k_positive
  have hb := nonlinear_le_coordinate G (mul_nonneg hσ.le R.k_positive.le) x
  rw [R.referenceSpeed.groundParameter_density R.k_positive,
    R.referenceSpeed.ground_coordinate R.k_positive G] at hb
  change nonlinear (σ*R.k) R.density x ≤ (σ*R.k/R.k)*R.referenceSpeed.q x at hb
  have he : σ*R.k/R.k=σ := mul_div_cancel_right₀ _ R.k_positive.ne'
  rw [he] at hb
  exact ⟨div_nonneg (nonlinear_bounds R.density_properties.1 R.density_properties.2.1
    (mul_nonneg hσ.le R.k_positive.le) x).1 hσ.le,(div_le_iff₀ hσ).2 (by nlinarith)⟩

/--
Exact identity `R.filter hσ x=0`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_left` rewrites with this identity
to establish the identity `R.contactSlope hσ (R.referenceSpeed.X 0)=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_bounds`,
`chebyshev2.PrescribedSpeed.SpeedData.q_zero_left` with the arguments shown in the proof.
-/
theorem filter_zero_left {x : ℝ} (hx : x ≤ R.referenceSpeed.X 0) : R.filter hσ x=0 := by
  have hb := R.filter_bounds hσ x
  rw [R.referenceSpeed.q_zero_left hx] at hb
  exact le_antisymm hb.2 hb.1

/--
The actual derivative at the stated point: `HasDerivAt R.referenceSpeed.q (R.k*R.density x-Q
(R.referenceSpeed.q x)) x`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (R.contactSlope hσ)
(-R.contactDamping hσ x*R.contactSlope hσ x+R.contactForcing hσ x) x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.coordinate_derivative`
with the arguments shown in the proof.
-/
theorem coordinate_derivative (x : ℝ) : HasDerivAt R.referenceSpeed.q
    (R.k*R.density x-Q (R.referenceSpeed.q x)) x :=
  R.profile.coordinate_derivative R.k_positive x

/--
The stated quantitative bound `0 ≤ R.k*R.density x-Q (R.referenceSpeed.q x)`.

Use: `chebyshev2.Calibration.ReferenceData.contactForcing_nonneg` uses this bound to
establish the stated quantitative bound `0 ≤ R.contactForcing hσ x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `R.referenceSpeed.q x ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under
each of these mutually exclusive hypotheses.
-/
theorem coordinate_derivative_nonneg (x : ℝ) : 0 ≤ R.k*R.density x-Q (R.referenceSpeed.q x) := by
  -- Separate `R.referenceSpeed.q x ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each
  -- of these mutually exclusive hypotheses.
  rw [R.density_formula]
  change 0 ≤ R.speed (R.referenceSpeed.q x)
  have hq := R.referenceSpeed.q_mem x
  by_cases hi : R.referenceSpeed.q x ∈ Ioo (0:ℝ) 2
  · exact (R.speed_positive hi).le
  · rcases Data.endpoint_cases hq hi with he | he <;>
      simp only [speed,he,R.amplitude_zero,R.amplitude_two,Q,zero_pow (by decide : 2 ≠ 0),
        mul_zero,zero_mul,sub_self,sub_zero,le_refl]

/--
The actual derivative at the stated point: `HasDerivAt (R.contact hσ) (R.contactSlope hσ x) x`.

Use: `chebyshev2.Calibration.ReferenceData.J_contact_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun x =>
(R.calibration hσ hb hω).J (R.contact hσ x)) ((R.calibration hσ hb hω).Gamma
(R.referenceSpeed.q x)-(R.filter hσ x)^2) x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.coordinate_derivative`,
`chebyshev2.Calibration.ReferenceData.filter_derivative` with the arguments shown in the
proof.
-/
theorem contact_derivative (x : ℝ) : HasDerivAt (R.contact hσ) (R.contactSlope hσ x) x := by
  convert! (R.coordinate_derivative x).sub (R.filter_derivative hσ x) using 1
  dsimp [contactSlope]
  ring

/--
The actual derivative at the stated point: `HasDerivAt (R.contactSlope hσ) (-R.contactDamping
hσ x*R.contactSlope hσ x+R.contactForcing hσ x) x`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_integral` uses this derivative
formula to establish `R.contactSlope hσ x= exp (-primitive
(R.contactDamping hσ) x)* (∫ t in R.referenceSpeed.X 0..x, exp (primitive (R.contactDamping hσ)
t)*R.contactForcing hσ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.coordinate_derivative`,
`chebyshev2.Calibration.ReferenceData.filter_derivative` with the arguments shown in the
proof.
-/
theorem contactSlope_derivative (x : ℝ) : HasDerivAt (R.contactSlope hσ)
    (-R.contactDamping hσ x*R.contactSlope hσ x+R.contactForcing hσ x) x := by
  have hq := R.coordinate_derivative x
  have hf := R.filter_derivative hσ x
  have hQ := hq.mul ((hasDerivAt_const x 2).sub hq)
  convert! ((hf.const_mul 2).add ((hf.pow 2).const_mul σ)).sub hQ using 1
  dsimp [contactSlope,contactDamping,contactForcing,Q]
  ring

/--
Continuity of the displayed function: `Continuous (R.contactSlope hσ)`.

Use: a standalone supporting continuity result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.2.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_c1`,
`chebyshev2.PrescribedSpeed.SpeedData.q_continuous` with the arguments shown in the proof.
-/
theorem contactSlope_continuous : Continuous (R.contactSlope hσ) := by
  unfold contactSlope Q
  exact ((continuous_const.mul (R.filter_c1 hσ).continuous).add
    (continuous_const.mul ((R.filter_c1 hσ).continuous.pow 2))).sub
      (R.referenceSpeed.q_continuous.mul (continuous_const.sub R.referenceSpeed.q_continuous))

/--
Continuity of the displayed function: `Continuous (R.contactDamping hσ)`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_integral` uses this continuity
result to establish `R.contactSlope hσ x= exp (-primitive
(R.contactDamping hσ) x)* (∫ t in R.referenceSpeed.X 0..x, exp (primitive (R.contactDamping hσ)
t)*R.contactForcing hσ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_c1` with
the arguments shown in the proof.
-/
theorem contactDamping_continuous : Continuous (R.contactDamping hσ) := by
  have hc := (R.filter_c1 hσ).continuous
  unfold contactDamping
  fun_prop

/--
Continuity of the displayed function: `Continuous (R.contactForcing hσ)`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_integral` uses this continuity
result to establish `R.contactSlope hσ x= exp (-primitive
(R.contactDamping hσ) x)* (∫ t in R.referenceSpeed.X 0..x, exp (primitive (R.contactDamping hσ)
t)*R.contactForcing hσ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_c1`,
`chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.Calibration.ReferenceData.density_continuous` with the arguments shown in the
proof.
-/
theorem contactForcing_continuous : Continuous (R.contactForcing hσ) := by
  have hc := (R.filter_c1 hσ).continuous
  have hq := R.referenceSpeed.q_continuous
  have hm := R.density_continuous
  unfold contactForcing Q
  fun_prop

/--
The stated quantitative bound `0 ≤ R.contactForcing hσ x`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_positive` uses this bound to
establish the stated quantitative bound `0 < R.contactSlope hσ x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_mem`,
`chebyshev2.Calibration.ReferenceData.filter_bounds`,
`chebyshev2.Calibration.ReferenceData.coordinate_derivative_nonneg` with the arguments
shown in the proof.
-/
theorem contactForcing_nonneg (x : ℝ) : 0 ≤ R.contactForcing hσ x := by
  apply mul_nonneg _ (R.coordinate_derivative_nonneg x)
  have hq := (R.referenceSpeed.q_mem x).1
  have hf := (R.filter_bounds hσ x).1
  positivity

/--
Exact identity `R.contactSlope hσ (R.referenceSpeed.X 0)=0`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_integral` uses this identity to
establish the precise assertion is `R.contactSlope hσ x= exp (-primitive (R.contactDamping hσ)
x)* (∫ t in R.referenceSpeed.X 0..x, exp (primitive (R.contactDamping hσ) t)*R.contactForcing
hσ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.filter_zero_left`,
`chebyshev2.PrescribedSpeed.SpeedData.q_X` with the arguments shown in the proof.
-/
theorem contactSlope_left : R.contactSlope hσ (R.referenceSpeed.X 0)=0 := by
  rw [contactSlope,R.filter_zero_left hσ le_rfl,R.referenceSpeed.q_X (by norm_num)]
  norm_num [Q]

/--
The precise assertion is `R.contactSlope hσ x= exp (-primitive (R.contactDamping hσ) x)* (∫ t
in R.referenceSpeed.X 0..x, exp (primitive (R.contactDamping hσ) t)*R.contactForcing hσ t)`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_positive` rewrites with this
identity to prove the bound `0 < R.contactSlope hσ x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.variation_of_constants`,
`chebyshev2.Calibration.ReferenceData.contactDamping_continuous`,
`chebyshev2.Calibration.ReferenceData.contactForcing_continuous` with the arguments shown
in the proof.
-/
theorem contactSlope_integral (x : ℝ) : R.contactSlope hσ x=
    exp (-primitive (R.contactDamping hσ) x)*
      (∫ t in R.referenceSpeed.X 0..x,
        exp (primitive (R.contactDamping hσ) t)*R.contactForcing hσ t) :=
  variation_of_constants (R.contactDamping_continuous hσ) (R.contactForcing_continuous hσ)
    (R.contactSlope_derivative hσ) (R.contactSlope_left hσ) x

end
end chebyshev2.Calibration.ReferenceData
