import chebyshev2.Finite.SymmetricGain
import chebyshev2.Green.Energy

/-!
Article: chebyshev2, Theorem 1.1.
Normalized Energy.
Use: `chebyshev2.SineJacobi.normalized_gain_exact` feeds
`chebyshev2.Optimal.finiteGain_le_sine` (finite Gain le sine).
Proof chain: `chebyshev2.SineJacobi.normalized_gain_limit` — chebyshev2, Theorem 2.5; Finite
sine chain and limiting elliptic profile and energy.
-/
namespace chebyshev2
noncomputable section
open chebyshev1 Real

/--
Exact identity `sqrt ((N:ℝ)^3) = (N:ℝ)^(3/2:ℝ)`.

Use: `chebyshev2.Jacobi.normalized_endpoint` rewrites with this identity to establish exact
identity `I.delta*(2*I.epsilon N/I.delta*sqrt J.energy)/((N:ℝ)^(3/2:ℝ)*I.epsilon N) = 2*sqrt
J.normalizedEnergy`.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem sqrt_cube_eq_rpow (N : ℕ) : sqrt ((N:ℝ)^3) = (N:ℝ)^(3/2:ℝ) := by
  rw [show (N:ℝ)^3 = (N:ℝ)^2*(N:ℝ) by ring, sqrt_mul (sq_nonneg _),
    sqrt_sq (Nat.cast_nonneg N), show (3/2:ℝ) = 1+1/2 by norm_num,
    rpow_add_of_nonneg (Nat.cast_nonneg N) (by norm_num) (by norm_num), rpow_one,
    ← sqrt_eq_rpow]

namespace Recurrence
variable {N : ℕ} (R : Recurrence N) (I : SpectralInterval)
/--
Defines `normalizedGain` of type `` by `I.delta*R.method.realization.gain I
N/((N:ℝ)^(3/2:ℝ)*I.epsilon N)`.

Use: `chebyshev2.SineJacobi.normalized_gain_exact` rewrites with this definition to
establish exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedGain I = 2*sqrt
(chain N).normalizedEnergy`.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.
-/
def normalizedGain := I.delta*R.method.realization.gain I N/((N:ℝ)^(3/2:ℝ)*I.epsilon N)
/--
Defines `normalizedSymmetricGain` of type `` by `I.delta*R.symmetricGain
I/((N:ℝ)^(3/2:ℝ)*I.epsilon N)`.

Use: `chebyshev2.SineJacobi.normalized_symmetric_gain_exact` rewrites with this definition
to establish the identity `((recurrenceEquiv I N hN) (fiber N
hN)).val.normalizedSymmetricGain I = 2*sqrt (chain N).normalizedEnergy`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.
-/
def normalizedSymmetricGain := I.delta*R.symmetricGain I/((N:ℝ)^(3/2:ℝ)*I.epsilon N)
end Recurrence

namespace Jacobi
variable {N : ℕ} (J : Jacobi N) (I : SpectralInterval)
/--
Defines `normalizedEnergy` of type `` by `J.energy/(N:ℝ)^3`.

Use: `chebyshev2.Jacobi.normalized_endpoint` rewrites with this definition to establish
exact identity `I.delta*(2*I.epsilon N/I.delta*sqrt J.energy)/((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
2*sqrt J.normalizedEnergy`.

Article: chebyshev2, Theorem 1.2 via `chebyshev2.Optimal.greenConstant_le_sine`.
-/
def normalizedEnergy := J.energy/(N:ℝ)^3

/--
The stated quantitative bound `1 ≤ J.normalizedEnergy`.

Use: `chebyshev2.DualCertificate.uniform_sine_of_finite_lower` uses this bound to establish
the bound stated in that declaration.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.energy_ge_cube` with the arguments
shown in the proof.
-/
theorem normalizedEnergy_ge_one (hN : 0 < N) (ht : J.Terminal) : 1 ≤ J.normalizedEnergy := by
  apply (le_div_iff₀ (pow_pos (by exact_mod_cast hN) 3)).mpr
  simpa using J.energy_ge_cube hN ht

/--
Exact identity `I.delta*(2*I.epsilon N/I.delta*sqrt J.energy)/((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
2*sqrt J.normalizedEnergy`.

Use: `chebyshev2.Jacobi.normalizedGain_lower` rewrites with this identity to establish the
stated quantitative bound `2*sqrt J.normalizedEnergy ≤ (J.recurrence I (J.admissible I hN
ht)).normalizedGain I`.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalized_endpoint (hN : 0 < N) :
    I.delta*(2*I.epsilon N/I.delta*sqrt J.energy)/((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
      2*sqrt J.normalizedEnergy := by
  rw [normalizedEnergy, sqrt_div (show 0 ≤ J.energy from Finset.sum_nonneg (fun _ _ => sq_nonneg _)), sqrt_cube_eq_rpow]
  have hn : (N:ℝ)^(3/2:ℝ) ≠ 0 := (rpow_pos_of_pos (by exact_mod_cast hN) _).ne'
  have he : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
  field_simp [hn,he,I.delta_pos.ne']

/--
The stated quantitative bound `2*sqrt J.normalizedEnergy ≤ (J.recurrence I (J.admissible I hN
ht)).normalizedGain I`.

Use: `chebyshev2.DualCertificate.uniform_sine_of_finite_lower` uses this bound to establish
the bound stated in that declaration.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.normalized_endpoint`,
`chebyshev2.Jacobi.gain_lower_bound`, `chebyshev1.SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem normalizedGain_lower (hN : 0 < N) (ht : J.Terminal) :
    2*sqrt J.normalizedEnergy ≤
      (J.recurrence I (J.admissible I hN ht)).normalizedGain I := by
  rw [← J.normalized_endpoint I hN]
  apply div_le_div_of_nonneg_right ?_ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (one_div_pos.mpr (I.den_pos N)).le)
  exact mul_le_mul_of_nonneg_left (J.gain_lower_bound I hN ht) I.delta_pos.le

/--
The stated quantitative bound `2*sqrt J.normalizedEnergy ≤ (J.recurrence I (J.admissible I hN
ht)).normalizedSymmetricGain I`.

Use: `chebyshev2.Optimal.finiteSymmetricGain_lower` uses this bound to establish the stated
quantitative bound `2*sqrt (finiteEnergy n) ≤ finiteSymmetricGain I n`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.normalized_endpoint`,
`chebyshev2.Jacobi.symmetric_gain_bounds`, `chebyshev1.SpectralInterval.delta_pos` with
the arguments shown in the proof.
-/
theorem normalizedSymmetricGain_lower (hN : 0 < N) (ht : J.Terminal) :
    2*sqrt J.normalizedEnergy ≤
      (J.recurrence I (J.admissible I hN ht)).normalizedSymmetricGain I := by
  rw [← J.normalized_endpoint I hN]
  apply div_le_div_of_nonneg_right ?_ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (one_div_pos.mpr (I.den_pos N)).le)
  exact mul_le_mul_of_nonneg_left (J.symmetric_gain_bounds I hN ht).1 I.delta_pos.le

/--
The stated quantitative bound `(J.recurrence I (J.admissible I hN ht)).normalizedSymmetricGain
I ≤ (J.recurrence I (J.admissible I hN ht)).normalizedGain I`.

Use: `chebyshev2.Optimal.finiteSymmetricGain_le` uses this bound to establish the stated
quantitative bound `finiteSymmetricGain I n ≤ finiteGain I n`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Optimal.symmetricGainConstant_bounds`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.symmetric_gain_bounds`,
`chebyshev1.SpectralInterval.delta_pos`, `chebyshev1.SpectralInterval.den_pos` with the
arguments shown in the proof.
-/
theorem normalizedSymmetricGain_le (hN : 0 < N) (ht : J.Terminal) :
    (J.recurrence I (J.admissible I hN ht)).normalizedSymmetricGain I ≤
      (J.recurrence I (J.admissible I hN ht)).normalizedGain I := by
  apply div_le_div_of_nonneg_right ?_ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (one_div_pos.mpr (I.den_pos N)).le)
  exact mul_le_mul_of_nonneg_left (J.symmetric_gain_bounds I hN ht).2 I.delta_pos.le

end Jacobi

namespace SineJacobi

/--
Exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedGain I = 2*sqrt (chain
N).normalizedEnergy`.

Use: `chebyshev2.Optimal.finiteGain_le_sine` rewrites with this identity to establish the
stated quantitative bound `finiteGain I n ≤ 2*sqrt (SineJacobi.chain (n+1)).normalizedEnergy`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.normalized_gain_limit`.

Proof: Use the identities/estimates `chebyshev2.SineJacobi.gain_exact`,
`chebyshev2.Jacobi.normalized_endpoint` with the arguments shown in the proof.
-/
theorem normalized_gain_exact (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedGain I =
      2*sqrt (chain N).normalizedEnergy := by
  rw [Recurrence.normalizedGain, gain_exact I N hN]
  exact (chain N).normalized_endpoint I hN

/--
Exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedSymmetricGain I = 2*sqrt
(chain N).normalizedEnergy`.

Use: `chebyshev2.SineJacobi.normalized_symmetric_gain_limit` uses this identity to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun n
: ℕ => ((recurrenceEquiv I (n+1) (by omega)) (fiber (n+1) (by
omega))).val.normalizedSymmetricGain I) atTop (𝓝 (2*sqrt energy))`.

Article: chebyshev2, Theorem 1.1.

Proof: Use the identities/estimates `chebyshev2.SineJacobi.symmetric_gain_exact`,
`chebyshev2.Jacobi.normalized_endpoint` with the arguments shown in the proof.
-/
theorem normalized_symmetric_gain_exact (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedSymmetricGain I =
      2*sqrt (chain N).normalizedEnergy := by
  rw [Recurrence.normalizedSymmetricGain, symmetric_gain_exact I N hN]
  exact (chain N).normalized_endpoint I hN

end SineJacobi
end
end chebyshev2
