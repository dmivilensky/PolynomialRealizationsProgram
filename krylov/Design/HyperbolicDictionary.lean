import krylov.Design.SharpLobatto
import krylov.Design.PoissonMajorants
import chebyshev1.Chebyshev.Amplification
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
Article: main_krylov, apC:eq:theta and lem:chebyshev-design.
Use: identify the genuine physical-interval Chebyshev scale with sech(m*theta),
and prove the source's exact half-angle dictionary and two condition-number
bounds. Reuse the earlier Chebyshev arsinh normalization and gap estimate.
Source: the Chebyshev formalization and elementary hyperbolic inversion.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young

/-- The actual positive hyperbolic spacing of the physical spectral interval.
Article: main_krylov, apC:eq:theta. -/
def designSpacing (I : chebyshev1.SpectralInterval) : ℝ :=
  2 * arsinh (sqrt (I.mu / I.delta))

/-- The original spectral spacing is strictly positive.
Article: main_krylov, apC:eq:theta. -/
theorem designSpacing_pos (I : chebyshev1.SpectralInterval) : 0 < designSpacing I :=
  mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (sqrt_pos.mpr (div_pos I.mu_pos I.delta_pos)))

/-- The genuine spacing has the article's exact extrapolation parameter.
Article: main_krylov, apC:eq:theta. -/
theorem cosh_designSpacing (I : chebyshev1.SpectralInterval) : cosh (designSpacing I) = I.eta := by
  rw [designSpacing, chebyshev1.cosh_two_arsinh_sqrt _ (div_nonneg I.mu_pos.le I.delta_pos.le),
    I.eta_eq_one_add]
  ring

/-- The constructed spacing is exactly arcosh((kappa+1)/(kappa-1)).
Article: main_krylov, the definition preceding apC:eq:theta. -/
theorem designSpacing_eq_arcosh (I : chebyshev1.SpectralInterval) :
    designSpacing I = arcosh I.eta := by
  rw [← cosh_designSpacing I, Real.arcosh_cosh (designSpacing_pos I).le]

/-- Every original Chebyshev degree scale is the literal hyperbolic-secant sample.
Article: main_krylov, lem:chebyshev-design. -/
theorem epsilon_eq_sech (I : chebyshev1.SpectralInterval) (m : ℕ) :
    I.epsilon m = sech ((m : ℝ) * designSpacing I) := by
  rw [I.epsilon_cosh, sech, designSpacing]
  rw [show 2 * (m : ℝ) * arsinh (sqrt (I.mu / I.delta)) =
    (m : ℝ) * (2 * arsinh (sqrt (I.mu / I.delta))) by ring, one_div]

/-- A positive spectral interval has a strictly positive upper endpoint.
Article: main_krylov, apC:eq:theta. -/
theorem upper_spectral_pos (I : chebyshev1.SpectralInterval) : 0 < I.L :=
  I.mu_pos.trans I.mu_lt_L

/-- The exact square-root gap dictionary for the source condition number.
Article: main_krylov, apC:eq:theta. -/
theorem sqrt_inverse_kappa_gap (I : chebyshev1.SpectralInterval) :
    sqrt (I.mu / I.delta) = (sqrt (I.kappa - 1))⁻¹ := by
  have he : I.kappa - 1 = I.delta / I.mu := by
    unfold chebyshev1.SpectralInterval.kappa chebyshev1.SpectralInterval.delta
    field_simp [I.mu_pos.ne']
  rw [he, Real.sqrt_div I.mu_pos.le, Real.sqrt_div I.delta_pos.le]
  field_simp

/-- The exact square-root condition-number ratio dictionary.
Article: main_krylov, apC:eq:theta. -/
theorem sqrt_inverse_kappa (I : chebyshev1.SpectralInterval) :
    sqrt I.mu / sqrt I.L = (sqrt I.kappa)⁻¹ := by
  rw [chebyshev1.SpectralInterval.kappa, Real.sqrt_div (upper_spectral_pos I).le]
  field_simp

/-- The source's exact half-angle sinh and tanh identities hold on the actual physical interval.
Article: main_krylov, apC:eq:theta. -/
theorem designSpacing_half_angle (I : chebyshev1.SpectralInterval) :
    sinh (designSpacing I / 2) = (sqrt (I.kappa - 1))⁻¹ ∧
      tanh (designSpacing I / 2) = (sqrt I.kappa)⁻¹ := by
  have hh : designSpacing I / 2 = arsinh (sqrt (I.mu / I.delta)) := by
    unfold designSpacing
    ring
  have he : 1 + I.mu / I.delta = I.L / I.delta := by
    unfold chebyshev1.SpectralInterval.delta
    field_simp [(sub_pos.mpr I.mu_lt_L).ne']
    ring
  rw [hh, Real.sinh_arsinh, Real.tanh_arsinh,
    Real.sq_sqrt (div_nonneg I.mu_pos.le I.delta_pos.le), he]
  refine ⟨sqrt_inverse_kappa_gap I, ?_⟩
  rw [Real.sqrt_div I.mu_pos.le, Real.sqrt_div (upper_spectral_pos I).le,
    ← sqrt_inverse_kappa I]
  field_simp [(sqrt_pos.mpr I.delta_pos).ne']

/-- The source's two nonasymptotic condition-number bounds for theta.
Article: main_krylov, apC:eq:theta.
Proof: the earlier sharp arsinh-gap estimate at the zero endpoint supplies the
lower bound; x<=sinh(x) gives arsinh(x)<=x for the upper bound. -/
theorem designSpacing_bounds (I : chebyshev1.SpectralInterval) :
    2 / sqrt I.kappa ≤ designSpacing I ∧
      designSpacing I ≤ 2 / sqrt (I.kappa - 1) := by
  have hl := I.arsinh_gap_lower 0 le_rfl I.mu_pos.le
  simp only [Real.sqrt_zero, sub_zero, zero_div, Real.arsinh_zero] at hl
  have hu : arsinh (sqrt (I.mu / I.delta)) ≤ sqrt (I.mu / I.delta) := by
    rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
    exact Real.self_le_sinh_iff.mpr (sqrt_nonneg _)
  constructor
  · unfold designSpacing
    rw [div_eq_mul_inv, ← sqrt_inverse_kappa I]
    exact mul_le_mul_of_nonneg_left hl (by norm_num)
  · calc
      designSpacing I ≤ 2 * sqrt (I.mu / I.delta) :=
        mul_le_mul_of_nonneg_left hu (by norm_num)
      _ = 2 / sqrt (I.kappa - 1) := by rw [sqrt_inverse_kappa_gap, div_eq_mul_inv]

/-- The sharp Chebyshev design theorem in the literal source hyperbolic notation.
Article: main_krylov, lem:chebyshev-design. -/
theorem chebyshev_design_extremum_sech (I : chebyshev1.SpectralInterval) (m : ℕ) :
    (∀ ν : ProbabilityMeasure (Spectrum I), christoffel m 0 (spectralCoordinate I) ν ≤
      sech ((m : ℝ) * designSpacing I) ^ 2) ∧
      christoffel m 0 (spectralCoordinate I) (lobattoProbability I m) =
        sech ((m : ℝ) * designSpacing I) ^ 2 := by
  simpa only [epsilon_eq_sech] using chebyshev_design_extremum I m

end
end krylov.Design
