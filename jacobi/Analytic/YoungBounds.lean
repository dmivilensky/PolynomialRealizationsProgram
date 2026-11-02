import jacobi.Comparison.RealOptimalEnergy
import jacobi.Analytic.YoungDerivative

/-!
Article: jacobi, Theorem 4.2.
The actual explicit analytic Young lower function bounds the same
ordinary real finite-fibre optimum used in Theorems A--B. Consequently
the original upper-minus-Young gap is nonnegative and vanishes at U.
OrderEnergyAnalytic proves analyticity of that same original upper function.
QuadraticContact and OptimalEnergyContact derive its quadratic contact and
the full optimizer-independent conclusions of Theorem 4.2.
Use: Theorem 4.2's contact argument has genuine beta-independent comparison bounds, without assuming a limiting optimizer is persymmetric.
-/
namespace jacobi.Parameter
noncomputable section
open Real jacobi.Comparison jacobi.GelfandLevitan jacobi.Variational

/-- The actual explicit Young calibration and actual upper constant squeeze the original real full-fibre optimum for every beta.
Use: Theorem 4.2's contact argument has genuine beta-independent comparison bounds, without assuming a limiting optimizer is persymmetric.
Article: jacobi, Theorem 4.2.
Proof: the sharp Young calibration is below the proved complete lower
constant. Both are finite by the actual candidate bound, so toReal
preserves the lower inequality and the source's exact spectral normalization. -/
theorem young_optimal_upper_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    youngLower a≤realOptimalEnergy a b ha hb ∧
      realOptimalEnergy a b ha hb≤persymmetricConstant a ha := by
  -- All bounds concern the ordinary real optimum over the complete original finite fibres.
  have hY := ENNReal.toReal_mono (besselLowerConstant_ne_top ha)
    (young_le_lowerConstant (jacobi.Bessel.edgeSpectrum a ha))
  rw [ENNReal.toReal_ofReal (jacobi.Young.youngValue_nonneg
    (jacobi.Bessel.edgeSpectrum a ha).second_pos.le),← youngLower_spectral ha] at hY
  exact ⟨hY.trans (realOptimalEnergy_bounds ha hb).1,(realOptimalEnergy_bounds ha hb).2⟩

/-- The original upper-minus-Young contact gap is nonnegative throughout the full source order range.
Use: once actual upper analyticity is proved, this supplies the local-minimum premise of the quadratic-contact proof in Theorem 4.2.
Article: jacobi, Theorem 4.2.
Proof: specialize the proved beta-independent full-fibre squeeze at beta=alpha and compose its two actual inequalities. -/
theorem upper_young_gap_nonneg {a:ℝ} (ha:-1<a) :
    0≤persymmetricConstant a ha-youngLower a :=
  sub_nonneg.mpr ((young_optimal_upper_bounds ha ha).1.trans (young_optimal_upper_bounds ha ha).2)

/-- The actual source upper-minus-Young contact gap vanishes exactly at U.
Use: Theorem 4.2's local contact has the exact original equality point, without a numerical evaluation or an assumed stationary upper function.
Article: jacobi, Theorem 4.2.
Proof: both independently proved original values are the exact rational two fifteenths. -/
theorem upper_young_gap_U (ha:-1<(1/2:ℝ)) :
    persymmetricConstant (1/2) ha-youngLower (1/2)=0 := by
  rw [half_sine_persymmetricConstant,youngLower_U,sub_self]

end
end jacobi.Parameter
