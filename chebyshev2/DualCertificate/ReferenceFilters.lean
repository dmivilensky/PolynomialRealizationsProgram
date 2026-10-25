import chebyshev2.DualCertificate.ReferenceCoordinate

/-!
Article: chebyshev2, Theorem 3.2.
The actual normalized reference filter on each closed half of F.1(R).
Use: `chebyshev2.Calibration.ReferenceData.normalizedDefect_zero` feeds
`chebyshev2.Calibration.ReferenceData.normalizedDefectRHS_zero` (normalized Defect RHS zero).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` —
chebyshev2, Theorem 3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set Real chebyshev2.DualCertificate
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
variable (R : chebyshev2.Calibration.ReferenceData) {σ : ℝ} (hσ : 0<σ)

/--
Defines `normalizedFilter` of type `ℝ` by `R.filter hσ (R.normalizedX t)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedFilter_derivative` uses this
definition to establish the derivative within the stated domain: `HasDerivWithinAt
(R.normalizedFilter hσ) (R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2-
2*R.normalizedFilter hσ t-σ*(R.normalizedFilter hσ t)^2)) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def normalizedFilter (t : ℝ) : ℝ := R.filter hσ (R.normalizedX t)
/--
Defines `normalizedReflectedFilter` of type `ℝ` by `R.filter hσ (-R.normalizedX t)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_derivative` uses this
definition to establish the derivative formula stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def normalizedReflectedFilter (t : ℝ) : ℝ := R.filter hσ (-R.normalizedX t)
/--
Defines `normalizedDefect` of type `ℝ` by `t^3-R.normalizedFilter hσ t`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedDefect_zero` rewrites with this
definition to establish the identity `R.normalizedDefect hσ 0=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def normalizedDefect (t : ℝ) : ℝ := t^3-R.normalizedFilter hσ t

 /--
Exact identity `R.density (R.normalizedX t)=(t*R.normalizedRoot t)^2`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedFilter_derivative` rewrites with this
identity to establish the derivative within the stated domain: `HasDerivWithinAt
(R.normalizedFilter hσ) (R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2-
2*R.normalizedFilter hσ t-σ*(R.normalizedFilter hσ t)^2)) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.density_formula`,
`chebyshev2.PrescribedSpeed.SpeedData.q_X`, `chebyshev2.DualCertificate.cube_mem` with
the arguments shown in the proof.
-/
theorem normalized_density {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    R.density (R.normalizedX t)=(t*R.normalizedRoot t)^2 := by
  rw [R.density_formula]
  change (R.amplitude (R.referenceSpeed.q (R.referenceSpeed.X (t^3))))^2=_
  rw [R.referenceSpeed.q_X (by
    have h := cube_mem ht
    exact ⟨h.1,h.2.trans (by norm_num)⟩),R.normalizedRoot_amplitude ht]

 /--
The derivative within the stated domain: `HasDerivWithinAt (R.normalizedFilter hσ)
(R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2- 2*R.normalizedFilter hσ
t-σ*(R.normalizedFilter hσ t)^2)) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedFilter_smooth` uses this derivative
formula to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (R.normalizedFilter hσ)
(Icc (0:ℝ) 1)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.filter_derivative`,
`chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed`,
`chebyshev2.Calibration.ReferenceData.normalized_density` with the arguments shown in the
proof.
-/
theorem normalizedFilter_derivative {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (R.normalizedFilter hσ)
      (R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2-
        2*R.normalizedFilter hσ t-σ*(R.normalizedFilter hσ t)^2)) (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_derivative`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed`,
  -- `chebyshev2.Calibration.ReferenceData.normalized_density` with the arguments shown in
  -- the proof.
  have h := (R.filter_derivative hσ (R.normalizedX t)).comp_hasDerivWithinAt
    (h := R.normalizedX) t (R.normalizedX_derivative_closed ht)
  rw [R.normalized_density ht] at h
  convert! h using 1
  dsimp only [normalizedFilter]
  ring

 /--
The derivative within the stated domain: `HasDerivWithinAt (R.normalizedReflectedFilter hσ)
(-R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2- 2*R.normalizedReflectedFilter hσ
t-σ*(R.normalizedReflectedFilter hσ t)^2)) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_smooth` uses this
derivative formula to establish smoothness to the stated order: `ContDiffOn ℝ ∞
(R.normalizedReflectedFilter hσ) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.filter_derivative`,
`chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed`,
`chebyshev2.Calibration.ReferenceData.normalized_density` with the arguments shown in the
proof.
-/
theorem normalizedReflectedFilter_derivative {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (R.normalizedReflectedFilter hσ)
      (-R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2-
        2*R.normalizedReflectedFilter hσ t-σ*(R.normalizedReflectedFilter hσ t)^2))
        (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_derivative`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed`,
  -- `chebyshev2.Calibration.ReferenceData.normalized_density` with the arguments shown in
  -- the proof.
  have h := (R.filter_derivative hσ (-R.normalizedX t)).comp_hasDerivWithinAt
    (h := fun t => -R.normalizedX t) t (R.normalizedX_derivative_closed ht).neg
  rw [R.density_reflection,R.normalized_density ht] at h
  convert! h using 1
  dsimp only [normalizedReflectedFilter]
  ring

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (R.normalizedFilter hσ) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedDefect_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (R.normalizedDefect hσ) (Icc (0:ℝ)
1)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedVelocity_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedRoot_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedFilter_derivative` with the arguments shown
in the proof.
-/
theorem normalizedFilter_smooth : ContDiffOn ℝ ∞ (R.normalizedFilter hσ) (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.normalizedVelocity_smooth`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedRoot_smooth`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedFilter_derivative` with the arguments
  -- shown in the proof.
  let F : ℝ → ℝ → ℝ := fun t y => R.normalizedVelocity t*
    (R.k*(t*R.normalizedRoot t)^2-2*y-σ*y^2)
  have hp : MapsTo Prod.fst (Icc (0:ℝ) 1 ×ˢ (univ : Set ℝ)) (Icc (0:ℝ) 1) :=
    fun _ hp => hp.1
  have hv := R.normalizedVelocity_smooth.comp contDiffOn_fst hp
  have hz := R.normalizedRoot_smooth.comp contDiffOn_fst hp
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (f := F) (u := univ) _
    (fun _ ht => R.normalizedFilter_derivative hσ ht) (fun _ _ => mem_univ _)
  change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => R.normalizedVelocity p.1*
    (R.k*(p.1*R.normalizedRoot p.1)^2-2*p.2-σ*p.2^2)) _
  exact hv.mul (((contDiffOn_const.mul ((contDiffOn_fst.mul hz).pow 2)).sub
    (contDiffOn_const.mul contDiffOn_snd)).sub (contDiffOn_const.mul (contDiffOn_snd.pow 2)))

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (R.normalizedReflectedFilter hσ) (Icc (0:ℝ)
1)`.

Use: `chebyshev2.Calibration.ReferenceData.contactCoreIntegrand_smooth` uses this assertion
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (R.contactCoreIntegrand hσ) (Icc
(0:ℝ) 1)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedVelocity_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedRoot_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_derivative` with the
arguments shown in the proof.
-/
theorem normalizedReflectedFilter_smooth :
    ContDiffOn ℝ ∞ (R.normalizedReflectedFilter hσ) (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.normalizedVelocity_smooth`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedRoot_smooth`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_derivative` with the
  -- arguments shown in the proof.
  let F : ℝ → ℝ → ℝ := fun t y => -R.normalizedVelocity t*
    (R.k*(t*R.normalizedRoot t)^2-2*y-σ*y^2)
  have hp : MapsTo Prod.fst (Icc (0:ℝ) 1 ×ˢ (univ : Set ℝ)) (Icc (0:ℝ) 1) :=
    fun _ hp => hp.1
  have hv := R.normalizedVelocity_smooth.comp contDiffOn_fst hp
  have hz := R.normalizedRoot_smooth.comp contDiffOn_fst hp
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (f := F) (u := univ) _
    (fun _ ht => R.normalizedReflectedFilter_derivative hσ ht) (fun _ _ => mem_univ _)
  change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => -R.normalizedVelocity p.1*
    (R.k*(p.1*R.normalizedRoot p.1)^2-2*p.2-σ*p.2^2)) _
  exact hv.neg.mul (((contDiffOn_const.mul ((contDiffOn_fst.mul hz).pow 2)).sub
    (contDiffOn_const.mul contDiffOn_snd)).sub (contDiffOn_const.mul (contDiffOn_snd.pow 2)))

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (R.normalizedDefect hσ) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedDefect_cubic_quotient` uses this
assertion to construct witnesses satisfying `∃ g : ℝ → ℝ, ContDiffOn
ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, R.normalizedDefect hσ t=t^3*g t`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedFilter_smooth` with the arguments shown in
the proof.
-/
theorem normalizedDefect_smooth : ContDiffOn ℝ ∞ (R.normalizedDefect hσ) (Icc (0:ℝ) 1) :=
  (by fun_prop : ContDiffOn ℝ ∞ (fun t : ℝ => t^3) (Icc 0 1)).sub
    (R.normalizedFilter_smooth hσ)

 /--
Membership in the specified domain/enclosure: `R.normalizedFilter hσ t ∈ Icc (0:ℝ) (t^3)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedDefect_bounds` uses this assertion to
establish membership in the specified domain/enclosure: `R.normalizedDefect hσ t ∈ Icc (0:ℝ)
(t^3)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_bounds`,
`chebyshev2.PrescribedSpeed.SpeedData.q_X`, `chebyshev2.DualCertificate.cube_mem` with
the arguments shown in the proof.
-/
theorem normalizedFilter_bounds {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    R.normalizedFilter hσ t ∈ Icc (0:ℝ) (t^3) := by
  have h := R.filter_bounds hσ (R.normalizedX t)
  change _ ∈ Icc _ (R.referenceSpeed.q (R.referenceSpeed.X (t^3))) at h
  rw [R.referenceSpeed.q_X (by
    have h := cube_mem ht
    exact ⟨h.1,h.2.trans (by norm_num)⟩)] at h
  exact h

 /--
Membership in the specified domain/enclosure: `R.normalizedDefect hσ t ∈ Icc (0:ℝ) (t^3)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedDefect_order_seven` uses this
assertion to construct witnesses satisfying `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc
(0:ℝ) 1, 0≤R.normalizedDefect hσ t ∧ R.normalizedDefect hσ t≤C*t^7`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedFilter_bounds` with the arguments shown in
the proof.
-/
theorem normalizedDefect_bounds {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    R.normalizedDefect hσ t ∈ Icc (0:ℝ) (t^3) :=
  ⟨sub_nonneg.mpr (R.normalizedFilter_bounds hσ ht).2,
    sub_le_self _ (R.normalizedFilter_bounds hσ ht).1⟩

 /--
Exact identity `R.normalizedFilter hσ 0=0`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedDefect_zero` rewrites with this
identity to establish the identity `R.normalizedDefect hσ 0=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.filter_zero_left`
with the arguments shown in the proof.
-/
theorem normalizedFilter_zero : R.normalizedFilter hσ 0=0 :=
  R.filter_zero_left hσ (by simp only [normalizedX,zero_pow (by decide : 3≠0)]; exact le_rfl)

 /--
Exact identity `R.normalizedDefect hσ 0=0`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedDefectRHS_zero` rewrites with this
identity to establish the identity `R.normalizedDefectRHS hσ 0=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedFilter_zero` with the arguments shown in
the proof.
-/
theorem normalizedDefect_zero : R.normalizedDefect hσ 0=0 := by simp only [normalizedDefect,zero_pow (by decide : 3≠0),R.normalizedFilter_zero hσ,sub_zero]

end
end chebyshev2.Calibration.ReferenceData
