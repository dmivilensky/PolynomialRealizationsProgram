import chebyshev2.DualCertificate.NormalizedStates

/-!
Article: chebyshev2, Theorem 3.6.
The second closed half of F.1(F), with the actual reflected filters.
Use: `chebyshev2.DualCertificate.NormalizedCalibration.X_derivative` feeds
`chebyshev2.DualCertificate.NormalizedCalibration.X_smooth` (X smooth).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace chebyshev2.DualCertificate.NormalizedCalibration
noncomputable section
open Set Real chebyshev2.Calibration chebyshev2.Calculus
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (N : chebyshev2.DualCertificate.NormalizedCalibration)
  (hΓ : ∀ q∈Icc (0:ℝ) 2, N.calibration.Gamma (2-q)=N.calibration.Gamma q)
  {κ s : ℝ} (hκ : 0<κ)

/--
Defines `reflectedFilter` of type `ℝ` by `N.calibration.leftFilter hκ s (2-t^3)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.reflectedFilter_derivative` uses
this definition to establish the actual derivative at the stated point: `HasDerivAt
(N.reflectedFilter hκ s) (-N.velocity κ t* (s*(t*N.root κ t)^2-2*N.reflectedFilter hκ s
t-(N.reflectedFilter hκ s t)^2)) t`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.R_smooth`.
-/
def reflectedFilter (s t : ℝ) : ℝ := N.calibration.leftFilter hκ s (2-t^3)
/--
Defines `reflectedLinear` of type `ℝ` by `N.calibration.leftLinear hκ (2-t^3)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.reflectedLinear_derivative` uses
this definition to establish the actual derivative at the stated point: `HasDerivAt
(N.reflectedLinear hκ) (-N.velocity κ t* (κ*(t*N.root κ t)^2-2*N.reflectedLinear hκ t)) t`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth`.
-/
def reflectedLinear (t : ℝ) : ℝ := N.calibration.leftLinear hκ (2-t^3)

/--
Continuity of the displayed function: `Continuous (N.reflectedFilter hκ s)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.reflectedFilter_smooth` uses this
continuity result to establish smoothness to the stated order: `ContDiffOn ℝ ∞
(N.reflectedFilter hκ s) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.R_smooth`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.leftFilter_continuous`
with the arguments shown in the proof.
-/
theorem reflectedFilter_continuous (hs : 0≤s) : Continuous (N.reflectedFilter hκ s) :=
  (N.calibration.leftFilter_continuous hκ hs).comp (by fun_prop)

/--
Continuity of the displayed function: `Continuous (N.reflectedLinear hκ)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.reflectedLinear_smooth` uses this
continuity result to establish smoothness to the stated order: `ContDiffOn ℝ ∞
(N.reflectedLinear hκ) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.leftLinear_continuous`
with the arguments shown in the proof.
-/
theorem reflectedLinear_continuous : Continuous (N.reflectedLinear hκ) :=
  (N.calibration.leftLinear_continuous hκ).comp (by fun_prop)

include hΓ in
/--
The actual derivative at the stated point: `HasDerivAt (N.reflectedFilter hκ s) (-N.velocity κ
t* (s*(t*N.root κ t)^2-2*N.reflectedFilter hκ s t-(N.reflectedFilter hκ s t)^2)) t`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.reflectedFilter_smooth` uses this
derivative formula to establish smoothness to the stated order: `ContDiffOn ℝ ∞
(N.reflectedFilter hκ s) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.R_smooth`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem reflectedFilter_derivative (hs : 0≤s) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (N.reflectedFilter hκ s) (-N.velocity κ t*
      (s*(t*N.root κ t)^2-2*N.reflectedFilter hκ s t-(N.reflectedFilter hκ s t)^2)) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (N.calibration.leftFilter_derivative hκ hs
    (Side.q_interior Side.right ⟨ht.1,ht.2.le⟩)).comp
      (h := fun t : ℝ => 2-t^3) t (((hasDerivAt_id t).pow 3).const_sub 2)
  dsimp only [Side.q] at h
  rw [N.calibration.amplitude_reflection hκ hΓ,N.calibration.speed_reflection hκ hΓ,
    N.root_amplitude hκ ⟨ht.1.le,ht.2.le⟩,N.speed_factor hκ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  dsimp only [velocity,reflectedFilter,id_eq]
  field_simp [ht.1.ne',(N.speed_positive hκ ⟨ht.1.le,ht.2.le⟩).ne']
  ring

include hΓ in
/--
The actual derivative at the stated point: `HasDerivAt (N.reflectedLinear hκ) (-N.velocity κ t*
(κ*(t*N.root κ t)^2-2*N.reflectedLinear hκ t)) t`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.reflectedLinear_smooth` uses this
derivative formula to establish smoothness to the stated order: `ContDiffOn ℝ ∞
(N.reflectedLinear hκ) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem reflectedLinear_derivative {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (N.reflectedLinear hκ) (-N.velocity κ t*
      (κ*(t*N.root κ t)^2-2*N.reflectedLinear hκ t)) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (N.calibration.leftLinear_derivative hκ
    (Side.q_interior Side.right ⟨ht.1,ht.2.le⟩)).comp
      (h := fun t : ℝ => 2-t^3) t (((hasDerivAt_id t).pow 3).const_sub 2)
  dsimp only [Side.q] at h
  rw [N.calibration.amplitude_reflection hκ hΓ,N.calibration.speed_reflection hκ hΓ,
    N.root_amplitude hκ ⟨ht.1.le,ht.2.le⟩,N.speed_factor hκ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  dsimp only [velocity,reflectedLinear,id_eq]
  field_simp [ht.1.ne',(N.speed_positive hκ ⟨ht.1.le,ht.2.le⟩).ne']
  ring

include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.reflectedFilter hκ s) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.farFilter_smooth` uses this
assertion to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.farFilter hκ s) (Icc
(0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.R_smooth`.

Proof: Use the identities/estimates `chebyshev2.Calculus.regular_filter_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.velocity_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.root_smooth_fixed` with the arguments
shown in the proof.
-/
theorem reflectedFilter_smooth (hs : 0≤s) :
    ContDiffOn ℝ ∞ (N.reflectedFilter hκ s) (Icc (0:ℝ) 1) := by
  apply regular_filter_smooth (a := 1) (s := s) (N.velocity_smooth hκ).neg (N.root_smooth_fixed hκ)
    (N.reflectedFilter_continuous hκ hs).continuousOn
  intro t ht
  simpa only [one_mul] using N.reflectedFilter_derivative hΓ hκ hs ht

include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.reflectedLinear hκ) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.farLinear_smooth` uses this
assertion to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.farLinear hκ) (Icc
(0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth`.

Proof: Use the identities/estimates `chebyshev2.Calculus.regular_filter_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.velocity_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.root_smooth_fixed` with the arguments
shown in the proof.
-/
theorem reflectedLinear_smooth : ContDiffOn ℝ ∞ (N.reflectedLinear hκ) (Icc (0:ℝ) 1) := by
  apply regular_filter_smooth (s := κ) (a := 0) (N.velocity_smooth hκ).neg (N.root_smooth_fixed hκ)
    (N.reflectedLinear_continuous hκ).continuousOn
  intro t ht
  simpa only [zero_mul,sub_zero] using N.reflectedLinear_derivative hΓ hκ ht

/--
Defines `X` of type `ℝ` by `(N.calibration.comparisonSpeed hκ).X (t^3)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.X_continuous` uses this definition
to establish continuity of the displayed function: `Continuous (N.X hκ)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.
-/
def X (t : ℝ) : ℝ := (N.calibration.comparisonSpeed hκ).X (t^3)

/--
Continuity of the displayed function: `Continuous (N.X hκ)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.X_derivative_closed` uses this
continuity result to establish the derivative within the stated domain: `HasDerivWithinAt (N.X
hκ) (N.velocity κ t) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_continuous`
with the arguments shown in the proof.
-/
theorem X_continuous : Continuous (N.X hκ) :=
  (N.calibration.comparisonSpeed hκ).X_continuous.comp (by fun_prop)

/--
The actual derivative at the stated point: `HasDerivAt (N.X hκ) (N.velocity κ t) t`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.X_derivative_closed` uses this
derivative formula to establish the derivative within the stated domain: `HasDerivWithinAt (N.X
hκ) (N.velocity κ t) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem X_derivative {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (N.X hκ) (N.velocity κ t) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (N.calibration.comparisonX_derivative hκ (cube_interior ht)).comp
    (h := fun t : ℝ => t^3) t ((hasDerivAt_id t).pow 3)
  rw [N.speed_factor hκ ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  unfold velocity
  norm_num only [id_eq,Nat.cast_ofNat,show (3:ℕ)-1=2 by omega]
  field_simp [ht.1.ne',(N.speed_positive hκ ⟨ht.1.le,ht.2.le⟩).ne']

/--
The derivative within the stated domain: `HasDerivWithinAt (N.X hκ) (N.velocity κ t) (Icc (0:ℝ)
1) t`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.6.

Proof: Use the identities/estimates
`chebyshev2.Calculus.hasDerivWithinAt_Icc_of_continuous_derivative`,
`chebyshev2.DualCertificate.NormalizedCalibration.X_continuous`,
`chebyshev2.DualCertificate.NormalizedCalibration.velocity_smooth` with the arguments shown
in the proof.
-/
theorem X_derivative_closed {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (N.X hκ) (N.velocity κ t) (Icc (0:ℝ) 1) t :=
  hasDerivWithinAt_Icc_of_continuous_derivative (by norm_num)
    (N.X_continuous hκ).continuousOn (N.velocity_smooth hκ).continuousOn
    (fun _ ht => N.X_derivative hκ ht) t ht

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.X hκ) (Icc (0:ℝ) 1)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.6.

Proof: Use the identities/estimates
`chebyshev2.Calculus.contDiffOn_Icc_of_smooth_derivative`,
`chebyshev2.DualCertificate.NormalizedCalibration.X_continuous`,
`chebyshev2.DualCertificate.NormalizedCalibration.velocity_smooth` with the arguments shown
in the proof.
-/
theorem X_smooth : ContDiffOn ℝ ∞ (N.X hκ) (Icc (0:ℝ) 1) :=
  contDiffOn_Icc_of_smooth_derivative (by norm_num) (N.X_continuous hκ).continuousOn
    (N.velocity_smooth hκ) (fun _ ht => N.X_derivative hκ ht)

end
end chebyshev2.DualCertificate.NormalizedCalibration
