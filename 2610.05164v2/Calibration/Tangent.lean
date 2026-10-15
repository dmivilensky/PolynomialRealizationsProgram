import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-!
Article: 2610.05164v2, Lemma 11.
The tangent defect in (13).
Use: `«2610.05164v2».Calibration.Q_reflection` feeds
`«2610.05164v2».Comparison.Profile.reciprocal_reflection` (reciprocal reflection).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized` —
2610.05164v2, Theorem 3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration
noncomputable section

/--
Defines `Q` of type `ℝ` by `q*(2-q)`.

Use: `«2610.05164v2».Calibration.Q_le_one` uses this definition to establish the stated
quantitative bound `Q q ≤ 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def Q (q : ℝ) : ℝ := q*(2-q)

/--
Defines `rho` of type `ℝ` by `(n-ν)^2*(n+ν/2)`.

Use: `«2610.05164v2».Calibration.rho_eq_zero_iff` rewrites with this definition to establish
equivalence of the displayed criteria: `rho n ν=0 ↔ n=ν`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.pointwise_criterion`.
-/
def rho (n ν : ℝ) : ℝ := (n-ν)^2*(n+ν/2)

/--
Exact identity `n^3 = 3/2*ν*n^2-ν^3/2+rho n ν`.

Use: `«2610.05164v2».Calibration.Data.base_pointwise` uses this identity to establish the
precise assertion is `n^3+C.b*n^2+C.omega*f^2+ C.Vprime κ q*(κ*n^2-Q q)+C.omega*C.Jprime
h*(q^2+C.sigma*f^2-2*h)= rho n (C.amplitude κ q)+C.omega*C.T q h`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem tangent_identity (n ν : ℝ) :
    n^3 = 3/2*ν*n^2-ν^3/2+rho n ν := by unfold rho; ring

/--
The stated quantitative bound `0 ≤ rho n ν`.

Use: `«2610.05164v2».Calibration.Data.energy_eq_base_iff` uses this bound to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem rho_nonneg {n ν : ℝ} (hn : 0 ≤ n) (hν : 0 ≤ ν) : 0 ≤ rho n ν :=
  mul_nonneg (sq_nonneg _) (by positivity)

/--
Equivalence of the displayed criteria: `rho n ν=0 ↔ n=ν`.

Use: `«2610.05164v2».Calibration.Data.energy_eq_base_iff` uses this identity to establish the
identity stated in that declaration.

Article: 2610.05164v2, Proposition 5 via
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem rho_eq_zero_iff {n ν : ℝ} (hn : 0 ≤ n) (hν : 0 ≤ ν) :
    rho n ν=0 ↔ n=ν := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
    · have : n=0 ∧ ν=0 := by constructor <;> linarith
      simp [this.1,this.2]
  · rintro rfl
    simp [rho]

/--
The stated quantitative bound `0 ≤ Q q`.

Use: `«2610.05164v2».Calibration.Data.amplitude_cube_bound_compact` uses this bound to
establish constructs witnesses with the exact properties `∃ A : ℝ, 0 < A ∧ ∀ κ ∈ K, ∀ q ∈ Icc
(0:ℝ) 2, (C.amplitude κ q)^3 ≤ A*Q q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem Q_nonneg {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 2) : 0 ≤ Q q :=
  mul_nonneg hq.1 (sub_nonneg.mpr hq.2)

/--
The stated quantitative bound `0 < Q q`.

Use: `«2610.05164v2».Calibration.Data.Q_div_speed_amplitude` uses this bound to establish the
stated quantitative bound `Q q/(C.speed κ q*C.amplitude κ q) ≤ 1/(2*C.b)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem Q_positive {q : ℝ} (hq : q ∈ Set.Ioo (0:ℝ) 2) : 0 < Q q :=
  mul_pos hq.1 (sub_pos.mpr hq.2)

/--
The stated quantitative bound `Q q ≤ 1`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Q_le_one (q : ℝ) : Q q ≤ 1 := by dsimp [Q]; nlinarith [sq_nonneg (q-1)]

/--
Exact identity `Q (2-q)=Q q`.

Use: `«2610.05164v2».Calibration.Data.amplitude_reflection` uses this identity to establish
exact identity `C.amplitude κ (2-q)=C.amplitude κ q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Q_reflection (q : ℝ) : Q (2-q)=Q q := by unfold Q; ring

end
end «2610.05164v2».Calibration
