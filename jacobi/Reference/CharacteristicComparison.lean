import jacobi.Reference.NegativeShift

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The two original printed characteristics have the same genuine leading
limit on the identical shifted negative-energy path. Their actual
complex quotient therefore tends to one. This is the normalization
comparison used to fix the constant in their relative product.
Use: compares the actual complex characteristics in characteristic_negative_ratio, including their previously fixed normalization.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual complex Bessel characteristic has its printed leading constant on the same negative-energy path as the original reference characteristic.
Use: compares the actual complex characteristics in characteristic_negative_ratio, including their previously fixed normalization.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: continuously embed the genuine shifted real leading limit and use reality of the original characteristic at each actual real energy. -/
theorem characteristicSigma_shifted_negative_complex_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => (((y^(a+1/2)*Real.exp (-y):ℝ):ℂ))*
      characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ))
      atTop (𝓝 ((Real.pi^a/(2*Real.sqrt Real.pi):ℝ):ℂ)) := by
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (characteristicSigma_shifted_negative_asymptotic ha)
  convert! hh using 1
  funext y
  dsimp only [Function.comp_apply]
  simp only [Complex.ofReal_mul,characteristicSigma_real]

/-- The quotient of the original reference and Bessel characteristics tends to exactly one on their common shifted negative-energy path.
Use: fixes the original relative canonical-product constant in Appendix C.2 from the actual printed normalizations.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: divide the two proved complex leading limits, whose common
printed constant is genuinely positive. The common real power and
exponential factors are nonzero at positive y and cancel exactly. -/
theorem characteristic_negative_ratio {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)/
      characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)) atTop (𝓝 1) := by
  -- Both limits belong to the actual source characteristics and the identical original energy, not just to products with their zeros.
  have hc : ((Real.pi^a/(2*Real.sqrt Real.pi):ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hh := (characteristicTau_negative_complex_asymptotic ha).div
    (characteristicSigma_shifted_negative_complex_asymptotic ha) hc
  rw [div_self hc] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr
    (mul_pos (Real.rpow_pos_of_pos hy _) (Real.exp_pos _)).ne')

end
end jacobi.Reference
