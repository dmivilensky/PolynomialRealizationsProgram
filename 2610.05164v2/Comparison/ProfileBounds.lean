import «2610.05164v2».Comparison.ProfileRegularity

/-!
Article: 2610.05164v2, Theorem 3.4.
Uniform ratios for the full comparison-profile class of Definition 10.
Use: `«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` feeds
`«2610.05164v2».Comparison.Profile.traceGradientQ_bound` (trace Gradient Q bound).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison.Profile
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Calibration
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : «2610.05164v2».Comparison.Profile κ)

/--
Defines `amplitudeBound` of type `ℝ` by `max (Classical.choose (isCompact_Icc.bddAbove_image
P.continuous)) 1`.

Use: `«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` uses this definition to establish
the stated quantitative bound `Q q/P.speed q ≤ P.C*P.amplitudeBound`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def amplitudeBound : ℝ := max (Classical.choose (isCompact_Icc.bddAbove_image P.continuous)) 1

/--
The stated quantitative bound `0 < P.amplitudeBound`.

Use: `«2610.05164v2».Comparison.Profile.determinantGradientQ_bound` uses this bound to
establish the stated quantitative bound `‖P.determinantGradientQ hκ s q r‖ ≤
(s/κ)^2*P.C*P.amplitudeBound+s*P.C`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem amplitudeBound_positive : 0 < P.amplitudeBound := lt_of_lt_of_le (by norm_num) (le_max_right _ _)

/--
The stated quantitative bound `P.amplitude q ≤ P.amplitudeBound`.

Use: `«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` uses this bound to establish the
stated quantitative bound `Q q/P.speed q ≤ P.C*P.amplitudeBound`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem amplitude_le_bound {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : P.amplitude q ≤ P.amplitudeBound :=
  (Classical.choose_spec (isCompact_Icc.bddAbove_image P.continuous)
    (mem_image_of_mem _ hq)).trans (le_max_left _ _)

/--
The stated quantitative bound `0 < P.speed q`.

Use: `«2610.05164v2».Comparison.Profile.C_positive` uses this bound to establish the stated
quantitative bound `0 < P.C`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.speed_eq` with the
arguments shown in the proof.
-/
theorem speed_pos {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) : 0 < P.speed q := by
  rw [P.speed_eq ⟨hq.1.le,hq.2.le⟩]
  exact P.speed_positive q hq

/--
The stated quantitative bound `(P.amplitude q)^2/P.speed q ≤ P.C ∧ Q q/(P.speed q*P.amplitude
q) ≤ P.C`.

Use: `«2610.05164v2».Comparison.Profile.C_positive` uses this bound to establish the stated
quantitative bound `0 < P.C`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.speed_pos`,
`«2610.05164v2».Calibration.Q_positive`, `«2610.05164v2».Comparison.Profile.speed_eq` with the
arguments shown in the proof.
-/
theorem ratio_bounds {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    (P.amplitude q)^2/P.speed q ≤ P.C ∧ Q q/(P.speed q*P.amplitude q) ≤ P.C := by
  -- Use the identities/estimates `«2610.05164v2».Comparison.Profile.speed_pos`,
  -- `«2610.05164v2».Calibration.Q_positive`, `«2610.05164v2».Comparison.Profile.speed_eq` with
  -- the arguments shown in the proof.
  have hv := P.positive q hq
  have hd := P.speed_pos hq
  have hQ := Q_positive hq
  have h1 : 0 ≤ (P.amplitude q)^2/P.speed q := by positivity
  have h2 : 0 ≤ Q q/(P.speed q*P.amplitude q) := by positivity
  have h3 : 0 ≤ (P.amplitude q)^3/Q q := by positivity
  have hb := P.bound q hq
  rw [← P.speed_eq ⟨hq.1.le,hq.2.le⟩] at hb
  constructor <;> linarith

/--
The stated quantitative bound `0 < P.C`.

Use: `«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` uses this bound to establish the
stated quantitative bound `Q q/P.speed q ≤ P.C*P.amplitudeBound`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.speed_pos`,
`«2610.05164v2».Comparison.Profile.ratio_bounds` with the arguments shown in the proof.
-/
theorem C_positive : 0 < P.C := by
  have hv := P.positive 1 (by norm_num)
  have hd := P.speed_pos (q := 1) (by norm_num)
  exact (div_pos (pow_pos hv 2) hd).trans_le (P.ratio_bounds (q := 1) (by norm_num)).1

/--
The stated quantitative bound `Q q/P.speed q ≤ P.C*P.amplitude q`.

Use: `«2610.05164v2».Comparison.Profile.Q_div_speed_le_bound` uses this bound to establish the
stated quantitative bound `Q q/P.speed q ≤ P.C*P.amplitudeBound`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.Profile.speed_pos`,
`«2610.05164v2».Comparison.Profile.ratio_bounds` with the arguments shown in the proof.
-/
theorem Q_div_speed_le_amplitude {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    Q q/P.speed q ≤ P.C*P.amplitude q := by
  have hd := P.speed_pos hq
  have hv := P.positive q hq
  have h := (div_le_iff₀ (mul_pos hd hv)).mp (P.ratio_bounds hq).2
  apply (div_le_iff₀ hd).2
  nlinarith

/--
The stated quantitative bound `Q q/P.speed q ≤ P.C*P.amplitudeBound`.

Use: `«2610.05164v2».Comparison.Profile.determinantGradientQ_bound` uses this bound to
establish the stated quantitative bound `‖P.determinantGradientQ hκ s q r‖ ≤
(s/κ)^2*P.C*P.amplitudeBound+s*P.C`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`«2610.05164v2».Comparison.Profile.Q_div_speed_le_amplitude`,
`«2610.05164v2».Comparison.Profile.amplitude_le_bound`,
`«2610.05164v2».Comparison.Profile.C_positive` with the arguments shown in the proof.
-/
theorem Q_div_speed_le_bound {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    Q q/P.speed q ≤ P.C*P.amplitudeBound :=
  (P.Q_div_speed_le_amplitude hq).trans
    (mul_le_mul_of_nonneg_left (P.amplitude_le_bound ⟨hq.1.le,hq.2.le⟩) P.C_positive.le)

end
end «2610.05164v2».Comparison.Profile
