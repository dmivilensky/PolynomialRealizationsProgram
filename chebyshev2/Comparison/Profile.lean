import chebyshev2.Calibration.Reciprocal

/-!
Article: chebyshev2, Proposition 8.
Definition 10's comparison-profile class and its actual calibration instance.
Use: `chebyshev2.Calibration.Data.comparisonProfile` feeds
`chebyshev2.Calibration.Data.comparisonProfile_A0` (comparison Profile A0).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Comparison
noncomputable section
open Set MeasureTheory chebyshev2.Calibration

/--
A continuous comparison amplitude with positive interior amplitude/speed, integrable inverse
speed and explicit endpoint-control bounds. These hypotheses justify the comparison-density
change of variables and singular integral formulas.

Use: `chebyshev2.Primal.determinant_profile_difference` uses this record of data and proof
obligations to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
structure Profile (κ : ℝ) where
  /-- Candidate comparison amplitude in the ground coordinate. -/
  amplitude : ℝ → ℝ
  /-- Continuity on the complete closed coordinate interval. -/
  continuous : ContinuousOn amplitude (Icc (0:ℝ) 2)
  /-- Nonnegativity, including the endpoints. -/
  nonneg : ∀ q ∈ Icc (0:ℝ) 2, 0 ≤ amplitude q
  /-- Strict positivity in the interior. -/
  positive : ∀ q ∈ Ioo (0:ℝ) 2, 0 < amplitude q
  /-- The induced coordinate speed is strictly positive in the interior. -/
  speed_positive : ∀ q ∈ Ioo (0:ℝ) 2, 0 < κ*(amplitude q)^2-Q q
  /-- The inverse speed is integrable, enabling the finite coordinate transformation. -/
  reciprocal_integrable : IntegrableOn (fun q => (κ*(amplitude q)^2-Q q)⁻¹) (Ioo (0:ℝ) 2)
  /-- Finite bound used for the singular-endpoint comparison integrands. -/
  C : ℝ
  /-- A common integrable-bound precursor for the three displayed amplitude/speed ratios. -/
  bound : ∀ q ∈ Ioo (0:ℝ) 2,
    (amplitude q)^2/(κ*(amplitude q)^2-Q q)+Q q/((κ*(amplitude q)^2-Q q)*amplitude q)+
      (amplitude q)^3/Q q ≤ C

end
end chebyshev2.Comparison

namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory chebyshev2.Comparison
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)

/--
Constructs `comparisonProfile` of type `Profile κ` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Calibration.Data.comparisonProfile_X` uses this definition to establish
exact identity `((C.comparisonProfile hκ).speedData hκ).X=(C.comparisonSpeed hκ).X`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonProfile : Profile κ where
  amplitude := C.amplitude κ
  continuous := C.amplitude_continuousOn_fixed hκ
  nonneg := fun q _ => C.amplitude_nonneg hκ q
  positive := fun q hq => (C.amplitude_spec hκ hq).1
  speed_positive := fun _ hq => C.speed_positive hκ hq
  reciprocal_integrable := C.reciprocal_integrable hκ
  C := 3/(2*κ)+1/(2*C.b)+Classical.choose (C.amplitude_cube_bound hκ)
  bound := by
    intro q hq
    have h1 := (C.amplitude_square_div_speed hκ hq).le
    have h2 := C.Q_div_speed_amplitude hκ hq
    have h3 := (Classical.choose_spec (C.amplitude_cube_bound hκ)).2 q ⟨hq.1.le,hq.2.le⟩
    have hb : (C.amplitude κ q)^3/chebyshev2.Calibration.Q q ≤ Classical.choose (C.amplitude_cube_bound hκ) :=
      (div_le_iff₀ (chebyshev2.Calibration.Q_positive hq)).2 h3
    exact add_le_add (add_le_add h1 h2) hb

end
end chebyshev2.Calibration.Data
