import chebyshev1.Chebyshev.Normalization

/-!
Article: chebyshev1, Theorem 4.2.
Coordinates.
Use: `chebyshev1.SpectralInterval.lambda_mem` feeds `chebyshev1.JacobiData.gain_eq_blocks`
(The supremum formula of Theorem 4.2, with exactly the article's z-coordinate domain).
Proof chain: `chebyshev1.JacobiData.gain_eq_blocks` — chebyshev1, Theorem 4.2; Block
determinants, first-variation kernel and gain.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — affine Chebyshev coordinates.
The needed form is proved here.
-/
namespace chebyshev1.SpectralInterval
noncomputable section
variable (I : SpectralInterval)

/--
Defines `lambda` of type `ℝ` by `(I.L + I.mu) / 2 - I.delta / 2 * x`.

Use: `chebyshev1.SpectralInterval.lambda_mem` uses this definition to establish membership
in the specified domain/enclosure: `I.lambda x ∈ Set.Icc I.mu I.L`.

Article: chebyshev1, Theorem 4.2 via `chebyshev1.JacobiData.gain_eq_blocks`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — affine Chebyshev
coordinates.
-/
def lambda (x : ℝ) : ℝ := (I.L + I.mu) / 2 - I.delta / 2 * x

/--
Exact identity `I.z (I.lambda x) = x`.

Use: `chebyshev1.JacobiData.gain_eq_blocks` rewrites with this identity to establish exact
identity `(J.realization I).gain I N = (2 / (I.delta * |J.den I N|)) * sSup (J.blockGainValues
N)`.

Article: chebyshev1, Theorem 4.2 via `chebyshev1.JacobiData.gain_eq_blocks`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — affine Chebyshev
coordinates.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
@[simp] theorem z_lambda (x : ℝ) : I.z (I.lambda x) = x := by
  dsimp [z, lambda]
  field_simp [ne_of_gt I.delta_pos]
  ring

/--
Exact identity `I.lambda (I.z x) = x`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Theorem 4.2.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — affine Chebyshev
coordinates.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
@[simp] theorem lambda_z (x : ℝ) : I.lambda (I.z x) = x := by
  dsimp [z, lambda]
  field_simp [ne_of_gt I.delta_pos]
  ring

/--
Membership in the specified domain/enclosure: `I.lambda x ∈ Set.Icc I.mu I.L`.

Use: `chebyshev1.JacobiData.gain_eq_blocks` uses this assertion to establish the identity
`(J.realization I).gain I N = (2 / (I.delta * |J.den I N|)) * sSup (J.blockGainValues N)`.

Article: chebyshev1, Theorem 4.2 via `chebyshev1.JacobiData.gain_eq_blocks`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — affine Chebyshev
coordinates.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.delta_pos` with the
arguments shown in the proof.
-/
theorem lambda_mem {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) : I.lambda x ∈ Set.Icc I.mu I.L := by
  have h1 := mul_le_mul_of_nonneg_left hx.1 I.delta_pos.le
  have h2 := mul_le_mul_of_nonneg_left hx.2 I.delta_pos.le
  dsimp [lambda, delta] at *
  constructor <;> nlinarith

end
end chebyshev1.SpectralInterval
