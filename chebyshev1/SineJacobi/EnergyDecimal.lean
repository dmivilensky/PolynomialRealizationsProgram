import chebyshev1.Numerics.EnergyWitnessGenerator

/-!
Article: chebyshev1, Theorem 5.2.
The paper's printed value is correct to seven decimal places.
Result: `chebyshev1.SineJacobi.sineEnergy_rounding` supplies the stated article conclusion.
-/
namespace chebyshev1.SineJacobi
open LeanCert.Core

set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

/--
Candidate integers are supplied by an untrusted generator; the kernel verifies them.

Constructs witnesses with the exact properties `∃ cs : List PanelCertificate,
panelCertificateCheck 2048 cs = true`.

Use: `chebyshev1.SineJacobi.sineEnergy_decimal` uses this identity to establish the stated
quantitative bound `(1.14269215:ℝ) < sineEnergy ∧ sineEnergy < (1.14269221:ℝ)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
private theorem verifiedQuadrature :
    ∃ cs : List PanelCertificate, panelCertificateCheck 2048 cs = true := by energy_certificate 2048

/--
A decimal enclosure of the actual elliptic-profile integral in Theorem 5.2.

The stated quantitative bound `(1.14269215:ℝ) < sineEnergy ∧ sineEnergy < (1.14269221:ℝ)`.

Use: `chebyshev1.SineJacobi.sineEnergy_rounding` uses this bound to establish the stated
quantitative bound `|sineEnergy-(1.1426922:ℝ)| < (0.00000005:ℝ)`.

Article: chebyshev1, Theorem 5.2.

Proof: Use the identities/estimates
`_private.chebyshev1.SineJacobi.EnergyDecimal.0.chebyshev1.SineJacobi.verifiedQuadrature`,
`chebyshev1.SineJacobi.panelCertificateCheck_correct`,
`chebyshev1.SineJacobi.sineEnergy_quadrature_error` with the arguments shown in the proof.
-/
theorem sineEnergy_decimal : (1.14269215:ℝ) < sineEnergy ∧ sineEnergy < (1.14269221:ℝ) := by
  -- Use the identities/estimates
  -- `_private.chebyshev1.SineJacobi.EnergyDecimal.0.chebyshev1.SineJacobi.verifiedQuadrature`,
  -- `chebyshev1.SineJacobi.panelCertificateCheck_correct`,
  -- `chebyshev1.SineJacobi.sineEnergy_quadrature_error` with the arguments shown in the
  -- proof.
  obtain ⟨cs, hc⟩ := verifiedQuadrature
  have hq := panelCertificateCheck_correct (by norm_num : 1 ≤ (2048:ℕ)) hc
  have he := sineEnergy_quadrature_error (N := 2048) (by norm_num)
  have he' : |sineEnergy-energyQuadrature 2048| < (25/10^9:ℝ) := by
    apply he.trans_lt
    norm_num
  have hb := abs_lt.mp he'
  constructor <;> linarith [hq.1, hq.2]

/--
The paper's printed value is correct to seven decimal places.

The stated quantitative bound `|sineEnergy-(1.1426922:ℝ)| < (0.00000005:ℝ)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 5.2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineEnergy_decimal` with the
arguments shown in the proof.
-/
theorem sineEnergy_rounding : |sineEnergy-(1.1426922:ℝ)| < (0.00000005:ℝ) := by
  rw [abs_lt]
  constructor <;> linarith [sineEnergy_decimal.1, sineEnergy_decimal.2]

end chebyshev1.SineJacobi
