import «2610.05164v2».DualCertificate.ReferenceGamma
import «2610.05164v2».Comparison.LeftFilters
import «2610.05164v2».Comparison.DefectBounds

/-!
Article: 2610.05164v2, Theorem 3.6.
F.1(C): the actual comparison cubic after removing t^3.
Use: `«2610.05164v2».DualCertificate.referenceNormalizedCalibration` feeds
`«2610.05164v2».DualCertificate.Data.normalization_calibration` (normalization calibration).
Proof chain: `«2610.05164v2».DualCertificate.Data.Admissible` — 2610.05164v2, Theorem E.1; Stability
of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Set Real «2610.05164v2».Calibration
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
A smooth normalized factor of the actual contact-minimizing amplitude. The factorization field
links endpoint-safe formulas to Gamma itself.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.coefficient_positive` uses this
record of data and proof obligations to prove the bound
`0<2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
structure NormalizedCalibration where
  /-- Actual contact-minimization data underlying the normalized comparison amplitude. -/
  calibration : «2610.05164v2».Calibration.Data
  /-- The smooth factor after dividing Gamma(t³) by Q(t³). -/
  gamma : ℝ → ℝ
  /-- All derivatives of the normalized factor exist on the closed interval, including endpoint extensions. -/
  smooth : ContDiffOn ℝ ∞ gamma (Icc 0 1)
  /-- The normalized comparison factor is nonnegative on its full parameter domain. -/
  nonneg : ∀ t ∈ Icc (0:ℝ) 1, 0≤gamma t
  /-- Exact factorization relating the normalized factor to the actual contact minimum; this is the bridge to the endpoint-safe formulas. -/
  factor : ∀ t ∈ Icc (0:ℝ) 1, calibration.Gamma (t^3)=«2610.05164v2».Calibration.Q (t^3)*gamma t

namespace NormalizedCalibration
variable (N : NormalizedCalibration)

/--
Defines `root` of type `ℝ` by `positiveRoot κ (t*(2-t^3))
(2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3))`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` uses this definition to
establish exact identity `0<N.root κ t ∧ cubic κ (t*(2-t^3))
(2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3)) (N.root κ t)=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def root (κ t : ℝ) : ℝ := positiveRoot κ (t*(2-t^3))
  (2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3))
/--
Defines `speed` of type `ℝ` by `2*t*(2-t^3)+ 2*(N.calibration.b+κ*N.calibration.omega*N.gamma
t)*(2-t^3)/N.root κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.speed_factor` uses this definition
to establish the identity `N.calibration.speed κ (t^3)=t^2*N.speed κ t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def speed (κ t : ℝ) : ℝ := 2*t*(2-t^3)+
  2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3)/N.root κ t

/--
The stated quantitative bound `0<2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth` uses this bound to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => N.root p.1 p.2)
(Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem` with the
arguments shown in the proof.
-/
theorem coefficient_positive {κ t : ℝ} (hκ : 0<κ) (ht : t ∈ Icc (0:ℝ) 1) :
    0<2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3) := by
  have hb := N.calibration.b_positive
  have ho := N.calibration.omega_nonneg
  have hg := N.nonneg t ht
  have hh : 0<2-t^3 := by linarith [(cube_mem ht).2]
  positivity

/--
Exact identity `0<N.root κ t ∧ cubic κ (t*(2-t^3))
(2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3)) (N.root κ t)=0`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.root_amplitude` uses this identity
to establish the identity `N.calibration.amplitude κ (t^3)=t*N.root κ t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.positiveRoot_spec`,
`«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.coefficient_positive` with the arguments
shown in the proof.
-/
theorem root_spec {κ t : ℝ} (hκ : 0<κ) (ht : t ∈ Icc (0:ℝ) 1) :
    0<N.root κ t ∧ cubic κ (t*(2-t^3))
      (2*(N.calibration.b+κ*N.calibration.omega*N.gamma t)*(2-t^3)) (N.root κ t)=0 :=
  positiveRoot_spec hκ (mul_nonneg ht.1 (by linarith [(cube_mem ht).2]))
    (N.coefficient_positive hκ ht)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => N.root p.1 p.2) (Ioi (0:ℝ) ×ˢ
Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.speed_smooth` uses this identity to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => N.speed p.1 p.2)
(Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.positiveRoot_contDiffOn`,
`«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.coefficient_positive` with the arguments
shown in the proof.
-/
theorem root_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => N.root p.1 p.2)
    (Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.positiveRoot_contDiffOn`,
  -- `«2610.05164v2».DualCertificate.cube_mem`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.coefficient_positive` with the
  -- arguments shown in the proof.
  have hg := N.smooth.comp contDiffOn_snd (fun (p : ℝ × ℝ) (hp : p ∈ Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1) => hp.2)
  have hq : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2*(2-p.2^3))
      (Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1) := by fun_prop
  have hc : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      2*(N.calibration.b+p.1*N.calibration.omega*N.gamma p.2)*(2-p.2^3))
      (Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1) :=
    (contDiffOn_const.mul (contDiffOn_const.add
      ((contDiffOn_fst.mul contDiffOn_const).mul hg))).mul (by fun_prop)
  exact positiveRoot_contDiffOn.comp (contDiffOn_fst.prodMk (hq.prodMk hc))
    (fun _ hp => ⟨hp.1,mul_nonneg hp.2.1 (by linarith [(cube_mem hp.2).2]),
      N.coefficient_positive hp.1 hp.2⟩)

/--
The stated quantitative bound `0<N.speed κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.X_derivative` uses this bound to
establish the actual derivative at the stated point: `HasDerivAt (N.X hκ) (N.velocity κ t) t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.coefficient_positive`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` with the arguments shown in
the proof.
-/
theorem speed_positive {κ t : ℝ} (hκ : 0<κ) (ht : t ∈ Icc (0:ℝ) 1) : 0<N.speed κ t := by
  unfold speed
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (mul_nonneg (by norm_num) ht.1) (by linarith [(cube_mem ht).2]))
    (div_pos (N.coefficient_positive hκ ht) (N.root_spec hκ ht).1)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => N.speed p.1 p.2) (Ioi (0:ℝ)
×ˢ Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_joint_continuous` uses
this identity to establish continuity of the displayed function: `Continuous (fun p :
CoefficientBox => N.certificateB P side p.1.property ξ₀ ξ₁ χ τ p.2.1 p.2.2.1 p.2.2.2.1
p.2.2.2.2)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_spec` with the arguments shown in
the proof.
-/
theorem speed_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => N.speed p.1 p.2)
    (Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1) := by
  have hg := N.smooth.comp contDiffOn_snd (fun (p : ℝ × ℝ) (hp : p ∈ Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1) => hp.2)
  exact (by fun_prop : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2*p.2*(2-p.2^3))
    (Ioi (0:ℝ) ×ˢ Icc (0:ℝ) 1)).add
    (((contDiffOn_const.mul (contDiffOn_const.add
      ((contDiffOn_fst.mul contDiffOn_const).mul hg))).mul (by fun_prop)).div N.root_smooth
      (fun _ hp => (N.root_spec hp.1 hp.2).1.ne'))

/--
Exact identity `N.calibration.amplitude κ (t^3)=t*N.root κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.speed_factor` rewrites with this
identity to establish the identity `N.calibration.speed κ (t^3)=t^2*N.speed κ t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem root_amplitude {κ t : ℝ} (hκ : 0<κ) (ht : t ∈ Icc (0:ℝ) 1) :
    N.calibration.amplitude κ (t^3)=t*N.root κ t := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : t=0
  · simp [hz,N.calibration.amplitude_zero]
  have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hq := Side.q_interior Side.left ⟨hp,ht.2⟩
  change t^3 ∈ Ioo (0:ℝ) 2 at hq
  apply N.calibration.amplitude_unique hκ hq (mul_pos hp (N.root_spec hκ ht).1)
  have he := (N.root_spec hκ ht).2
  unfold Data.constant
  rw [N.factor _ ht]
  unfold cubic «2610.05164v2».Calibration.Q at *
  linear_combination t^3*he

/--
Exact identity `κ*(N.root κ t)^2=N.speed κ t+t*(2-t^3)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.speed_factor` uses this identity to
establish exact identity `N.calibration.speed κ (t^3)=t^2*N.speed κ t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem speed_root {κ t : ℝ} (hκ : 0<κ) (ht : t ∈ Icc (0:ℝ) 1) :
    κ*(N.root κ t)^2=N.speed κ t+t*(2-t^3) := by
  have he := (N.root_spec hκ ht).2
  unfold cubic at he
  unfold speed
  field_simp [(N.root_spec hκ ht).1.ne']
  linear_combination he

/--
Exact identity `N.calibration.speed κ (t^3)=t^2*N.speed κ t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.X_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (N.X hκ)
(N.velocity κ t) t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_amplitude`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.speed_root` with the arguments shown in
the proof.
-/
theorem speed_factor {κ t : ℝ} (hκ : 0<κ) (ht : t ∈ Icc (0:ℝ) 1) :
    N.calibration.speed κ (t^3)=t^2*N.speed κ t := by
  unfold Data.speed
  rw [N.root_amplitude hκ ht]
  unfold «2610.05164v2».Calibration.Q
  linear_combination t^2*N.speed_root hκ ht

end NormalizedCalibration

/--
The literal reference/contact calibration supplies all fields of the normalization package; no
normalized coefficient is an additional assumption.

Use: `«2610.05164v2».DualCertificate.Data.normalization` uses this definition in the displayed
construction of `normalization`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def referenceNormalizedCalibration (R : «2610.05164v2».Calibration.ReferenceData)
    {σ b omega : ℝ} (hσ : 0<σ) (hb : 0<b) (ho : 0≤omega) : NormalizedCalibration where
  calibration := R.calibration hσ hb ho
  gamma := R.normalizedGamma hσ
  smooth := R.normalizedGamma_smooth hσ
  nonneg := fun _ ht => R.normalizedGamma_nonneg hσ ht
  factor := fun _ ht => R.normalizedGamma_factor hσ hb ho ht

end
end «2610.05164v2».DualCertificate
