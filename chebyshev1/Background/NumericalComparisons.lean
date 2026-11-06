import chebyshev1.SineJacobi.EnergyDecimal

/-! Rounded gain constants and percentage comparisons printed in the article. -/
namespace chebyshev1.SineJacobi
noncomputable section

theorem gainConstant_rounding :
    |2*Real.sqrt sineEnergy - (2.137936 : ℝ)| < 0.0000005 := by
  obtain ⟨hl, hu⟩ := sineEnergy_decimal
  have hs := Real.sqrt_nonneg sineEnergy
  have he := Real.sq_sqrt (by linarith : 0 ≤ sineEnergy)
  rw [abs_lt]
  constructor <;> nlinarith

theorem relativeGainImprovement_rounding :
    |100*(1-Real.sqrt (3*sineEnergy/4)) - (7.4 : ℝ)| < 0.05 := by
  obtain ⟨hl, hu⟩ := sineEnergy_decimal
  have hs := Real.sqrt_nonneg (3*sineEnergy/4)
  have he := Real.sq_sqrt (by linarith : 0 ≤ 3*sineEnergy/4)
  rw [abs_lt]
  constructor <;> nlinarith

theorem squaredGainImprovement_rounding :
    |100*(1-3*sineEnergy/4) - (14.3 : ℝ)| < 0.05 := by
  obtain ⟨hl, hu⟩ := sineEnergy_decimal
  rw [abs_lt]
  constructor <;> linarith

theorem universalLowerGap_rounding :
    |100*(Real.sqrt sineEnergy-1) - (7 : ℝ)| < 0.5 := by
  obtain ⟨hl, hu⟩ := sineEnergy_decimal
  have hs := Real.sqrt_nonneg sineEnergy
  have he := Real.sq_sqrt (by linarith : 0 ≤ sineEnergy)
  rw [abs_lt]
  constructor <;> nlinarith

theorem prefixGainConstant_rounding :
    |4/Real.sqrt 3 - (2.3094 : ℝ)| < 0.00005 := by
  have hs : 0 < (4 : ℝ)/Real.sqrt 3 := by positivity
  have he : ((4 : ℝ)/Real.sqrt 3)^2 = 16/3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [abs_lt]
  constructor <;> nlinarith

end
end chebyshev1.SineJacobi
