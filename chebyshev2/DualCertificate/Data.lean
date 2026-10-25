import chebyshev2.DualCertificate.RationalReference
import chebyshev2.DualCertificate.PolynomialPotential
import chebyshev2.DualCertificate.Coordinate
import chebyshev2.DualCertificate.Cells
import chebyshev2.Calibration.GlobalMinimum

/-!
Article: chebyshev2, Theorem 3.6.
Literal rational certificate data of Definition 7.
Use: `chebyshev2.DualCertificate.Data.Gamma_symmetric` feeds
`chebyshev2.DualCertificate.Data.comparisonS_continuous` (comparison S continuous).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.DualCertificate
noncomputable section

/--
Definition 7's rational dual-certificate data, comprising the reference profile, calibration
parameters, observation multipliers, polynomial state potential and cellwise price data.
Admissibility is proved or assumed separately by an explicit predicate.

Use: `chebyshev2.DualCertificate.Data.calibration_b` uses this record of data and proof
obligations to establish the identity `D.calibration.b=(D.b:ℝ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
structure Data where
  /-- Positive rational reference profile supplying the contact problem. -/
  reference : RationalReference
  /-- Rational determinant-observation scale. -/
  σ : ℚ
  /-- Positive rational reference energy/base parameter. -/
  b : ℚ
  /-- Nonnegative rational multiplier of the determinant observation. -/
  ω : ℚ
  /-- The observation scale is strictly positive. -/
  σ_pos : 0<σ
  /-- The reference base parameter is strictly positive. -/
  b_pos : 0<b
  /-- The determinant multiplier has the sign required by the dual energy inequality. -/
  ω_nonneg : 0≤ω
  /-- Rational polynomial state potential used in the pointwise differential inequality. -/
  potential : PolynomialPotential
  /-- Multiplier of the first fixed determinant observation. -/
  ξ₀ : ℚ
  /-- Multiplier of the second fixed determinant observation. -/
  ξ₁ : ℚ
  /-- Multiplier of the square-trace observation. -/
  χ : ℚ
  /-- Scalar coefficient entering the relaxed certificate value. -/
  τ : ℚ
  /-- Left/right cell decompositions carrying the piecewise affine price data. -/
  cells : Side → Cells

namespace Data
variable (D : Data)

/--
Defines `referenceData` of type `chebyshev2.Calibration.ReferenceData` by
`D.reference.referenceData (k := Real.pi^2/4) (div_pos (sq_pos_of_pos Real.pi_pos) (by
norm_num))`.

Use: `chebyshev2.DualCertificate.Data.Gamma_symmetric` uses this definition to establish
exact identity `D.calibration.Gamma (2-q)=D.calibration.Gamma q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def referenceData : chebyshev2.Calibration.ReferenceData :=
  D.reference.referenceData (k := Real.pi^2/4)
    (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))

/--
Defines `calibration` of type `chebyshev2.Calibration.Data` by `D.referenceData.calibration
(σ := (D.σ:ℝ)) (by exact_mod_cast D.σ_pos) (b := (D.b:ℝ)) (ω := (D.ω:ℝ)) (by exact_mod_cast
D.b_pos) (by exact_mod_cast D.ω_nonneg)`.

Use: `chebyshev2.DualCertificate.Data.Gamma_symmetric` uses this definition to establish
exact identity `D.calibration.Gamma (2-q)=D.calibration.Gamma q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def calibration : chebyshev2.Calibration.Data :=
  D.referenceData.calibration (σ := (D.σ:ℝ)) (by exact_mod_cast D.σ_pos)
    (b := (D.b:ℝ)) (ω := (D.ω:ℝ)) (by exact_mod_cast D.b_pos) (by exact_mod_cast D.ω_nonneg)

/--
Exact identity `D.calibration.sigma=(D.σ:ℝ)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.6.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem calibration_sigma : D.calibration.sigma=(D.σ:ℝ) := rfl
/--
Exact identity `D.calibration.b=(D.b:ℝ)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.6.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem calibration_b : D.calibration.b=(D.b:ℝ) := rfl
/--
Exact identity `D.calibration.omega=(D.ω:ℝ)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.6.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem calibration_omega : D.calibration.omega=(D.ω:ℝ) := rfl
/--
Exact identity `D.calibration.Gamma (2-q)=D.calibration.Gamma q`.

Use: `chebyshev2.DualCertificate.Data.boundary_residual` uses this identity to establish
exact identity `D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential
κ) Y 0=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.calibration_Gamma_reflection` with the arguments
shown in the proof.
-/
theorem Gamma_symmetric {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 2) :
    D.calibration.Gamma (2-q)=D.calibration.Gamma q :=
  D.referenceData.calibration_Gamma_reflection (by exact_mod_cast D.σ_pos)
    (by exact_mod_cast D.b_pos) (by exact_mod_cast D.ω_nonneg) q hq

end Data
end
end chebyshev2.DualCertificate
