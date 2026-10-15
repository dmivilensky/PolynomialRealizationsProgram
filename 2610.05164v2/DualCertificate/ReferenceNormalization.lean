import «2610.05164v2».DualCertificate.Coordinate
import «2610.05164v2».DualCertificate.CubicSmooth
import «2610.05164v2».Calibration.ReferenceProfile

/-!
Article: 2610.05164v2, Theorem 3.2.
The normalized reference cubic in F.1(R): the root and speed extend smoothly and remain strictly
positive at t=0.
Use: `«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_factor` feeds
`«2610.05164v2».Calibration.ReferenceData.normalizedX_derivative` (normalized X derivative).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized` —
2610.05164v2, Theorem 3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set «2610.05164v2».DualCertificate
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
variable (R : «2610.05164v2».Calibration.ReferenceData)

/--
Defines `normalizedRoot` of type `ℝ` by `positiveRoot R.k (t*(2-t^3)) (2*R.b
(t^3*(2-t^3))*(2-t^3))`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedRoot_amplitude` uses this definition
to establish the identity `R.amplitude (t^3)=t*R.normalizedRoot t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def normalizedRoot (t : ℝ) : ℝ := positiveRoot R.k (t*(2-t^3))
  (2*R.b (t^3*(2-t^3))*(2-t^3))

/--
Defines `normalizedSpeed` of type `ℝ` by `2*t*(2-t^3)+ 2*R.b
(t^3*(2-t^3))*(2-t^3)/R.normalizedRoot t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_factor` uses this definition to
establish exact identity `R.speed (t^3)=t^2*R.normalizedSpeed t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def normalizedSpeed (t : ℝ) : ℝ := 2*t*(2-t^3)+
  2*R.b (t^3*(2-t^3))*(2-t^3)/R.normalizedRoot t

/--
Membership in the specified domain/enclosure: `t^3*(2-t^3) ∈ Icc (0:ℝ) 1`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedRoot_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedRoot (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem` with the
arguments shown in the proof.
-/
theorem normalized_coefficient_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    t^3*(2-t^3) ∈ Icc (0:ℝ) 1 := by
  have hc := cube_mem ht
  refine ⟨mul_nonneg hc.1 (by linarith [hc.2]),?_⟩
  nlinarith [sq_nonneg (t^3-1)]

/--
Exact identity `0<R.normalizedRoot t ∧ cubic R.k (t*(2-t^3)) (2*R.b (t^3*(2-t^3))*(2-t^3))
(R.normalizedRoot t)=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedRoot_amplitude` uses this identity to
establish exact identity `R.amplitude (t^3)=t*R.normalizedRoot t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem`,
`«2610.05164v2».Calibration.positiveRoot_spec` with the arguments shown in the proof.
-/
theorem normalizedRoot_spec {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0<R.normalizedRoot t ∧ cubic R.k (t*(2-t^3))
      (2*R.b (t^3*(2-t^3))*(2-t^3)) (R.normalizedRoot t)=0 := by
  have hc := cube_mem ht
  have hb := R.positive _ (normalized_coefficient_mem ht)
  exact positiveRoot_spec R.k_positive (mul_nonneg ht.1 (by linarith [hc.2]))
    (mul_pos (mul_pos (by norm_num) hb) (by linarith [hc.2]))

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedRoot (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedSpeed (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem`,
`«2610.05164v2».Calibration.positiveRoot_contDiffOn`, `«2610.05164v2».DualCertificate.cube_mem`
with the arguments shown in the proof.
-/
theorem normalizedRoot_smooth : ContDiffOn ℝ ∞ R.normalizedRoot (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem`,
  -- `«2610.05164v2».Calibration.positiveRoot_contDiffOn`,
  -- `«2610.05164v2».DualCertificate.cube_mem` with the arguments shown in the proof.
  have hb : ContDiffOn ℝ ∞ (fun t => R.b (t^3*(2-t^3))) (Icc (0:ℝ) 1) :=
    R.smooth.comp (by fun_prop) (fun _ ht => normalized_coefficient_mem ht)
  have hparam : ContDiffOn ℝ ∞ (fun t : ℝ =>
      (R.k,t*(2-t^3),2*R.b (t^3*(2-t^3))*(2-t^3))) (Icc 0 1) := by
    have hq : ContDiffOn ℝ ∞ (fun t : ℝ => t*(2-t^3)) (Icc 0 1) := by fun_prop
    have hc : ContDiffOn ℝ ∞ (fun t : ℝ => 2*R.b (t^3*(2-t^3))*(2-t^3))
        (Icc 0 1) := (contDiffOn_const.mul hb).mul (by fun_prop)
    exact contDiffOn_const.prodMk (hq.prodMk hc)
  change ContDiffOn ℝ ∞ ((fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1 p.2.2) ∘
    (fun t => (R.k,t*(2-t^3),2*R.b (t^3*(2-t^3))*(2-t^3)))) (Icc 0 1)
  apply positiveRoot_contDiffOn.comp hparam
  intro t ht
  have hc := cube_mem ht
  exact ⟨R.k_positive,mul_nonneg ht.1 (by linarith [hc.2]),
    mul_pos (mul_pos (by norm_num) (R.positive _ (normalized_coefficient_mem ht)))
      (by linarith [hc.2])⟩

/--
The stated quantitative bound `0<R.normalizedSpeed t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_derivative` uses this bound to
establish the derivative within the stated domain: `HasDerivWithinAt (R.normalizedDefect hσ)
(R.normalizedDefectRHS hσ t) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem`,
`«2610.05164v2».Calibration.ReferenceData.normalizedRoot_spec` with the arguments shown in the
proof.
-/
theorem normalizedSpeed_positive {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0<R.normalizedSpeed t := by
  -- Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedRoot_spec` with the arguments shown in
  -- the proof.
  have hc := cube_mem ht
  have hb := R.positive _ (normalized_coefficient_mem ht)
  have hr := (R.normalizedRoot_spec ht).1
  unfold normalizedSpeed
  exact add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg (by norm_num) ht.1)
    (by linarith [hc.2]))
    (div_pos (mul_pos (mul_pos (by norm_num) hb) (by linarith [hc.2])) hr)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedSpeed (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedVelocity_smooth` uses this assertion
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedVelocity (Icc (0:ℝ)
1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem`,
`«2610.05164v2».Calibration.ReferenceData.normalizedRoot_smooth`,
`«2610.05164v2».Calibration.ReferenceData.normalizedRoot_spec` with the arguments shown in the
proof.
-/
theorem normalizedSpeed_smooth : ContDiffOn ℝ ∞ R.normalizedSpeed (Icc (0:ℝ) 1) := by
  have hb : ContDiffOn ℝ ∞ (fun t => R.b (t^3*(2-t^3))) (Icc (0:ℝ) 1) :=
    R.smooth.comp (by fun_prop) (fun _ ht => normalized_coefficient_mem ht)
  exact (by fun_prop : ContDiffOn ℝ ∞ (fun t : ℝ => 2*t*(2-t^3)) (Icc 0 1)).add
    (((contDiffOn_const.mul hb).mul (by fun_prop)).div R.normalizedRoot_smooth
      (fun _ ht => (R.normalizedRoot_spec ht).1.ne'))

/--
Exact identity `R.amplitude (t^3)=t*R.normalizedRoot t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_factor` rewrites with this
identity to establish the identity `R.speed (t^3)=t^2*R.normalizedSpeed t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem normalizedRoot_amplitude {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    R.amplitude (t^3)=t*R.normalizedRoot t := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : t=0
  · simp [hz,R.amplitude_zero]
  have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hq := Side.q_interior Side.left ⟨hp,ht.2⟩
  change t^3 ∈ Ioo (0:ℝ) 2 at hq
  have hQ := «2610.05164v2».Calibration.Q_positive hq
  have hmem := Q_mem ⟨hq.1.le,hq.2.le⟩
  have hr := R.normalizedRoot_spec ht
  unfold amplitude root
  rw [ite_eq_left hQ,R.coefficient_eq hmem]
  apply positiveRoot_eq R.k_positive hQ.le
    (mul_pos (mul_pos (by norm_num) (R.positive _ hmem)) hQ) (mul_pos hp hr.1)
  have he : cubic R.k («2610.05164v2».Calibration.Q (t^3))
      (2*R.b («2610.05164v2».Calibration.Q (t^3))*«2610.05164v2».Calibration.Q (t^3))
      (t*R.normalizedRoot t)=t^3*cubic R.k (t*(2-t^3))
        (2*R.b (t^3*(2-t^3))*(2-t^3)) (R.normalizedRoot t) := by
    unfold cubic «2610.05164v2».Calibration.Q
    ring
  rw [he,hr.2,mul_zero]

/--
Exact identity `R.speed (t^3)=t^2*R.normalizedSpeed t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedX_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt R.normalizedX
(R.normalizedVelocity t) t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedSpeed_factor {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    R.speed (t^3)=t^2*R.normalizedSpeed t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hr := R.normalizedRoot_spec ht
  have he := hr.2
  unfold cubic at he
  unfold speed normalizedSpeed «2610.05164v2».Calibration.Q
  rw [R.normalizedRoot_amplitude ht]
  field_simp [(R.normalizedRoot_spec ht).1.ne']
  linear_combination t^2*he

end
end «2610.05164v2».Calibration.ReferenceData
