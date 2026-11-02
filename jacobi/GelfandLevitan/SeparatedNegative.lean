import jacobi.GelfandLevitan.NegativeSlopeComparison
import jacobi.GelfandLevitan.MidpointProductFactorization

/-!
Article: jacobi, Proposition C.2.
The true negative-axis leading normalizations and the proved global
separated-product factorization force one actual separated class to be
Dirichlet. The class assignment, the remaining Robin parameter and its
vanishing require the subsequent finer comparison.
Use: the separated-characteristic boundary comparison keeps the actual source energy c_0-y^2 explicit without repeating long coercions.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original shifted negative-energy path in the genuine complex energy plane.
Use: the separated-characteristic boundary comparison keeps the actual source energy c_0-y^2 explicit without repeating long coercions.
Article: jacobi, Proposition C.2.
-/
def shiftedNegativeEnergy (a y : ℝ) : ℂ := ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)

/-- The actual original midpoint value divided by y*a_0 tends to zero on the shifted negative axis.
Use: separatedCharacteristic_negative_leading identifies the leading coefficient of each genuine original boundary determinant.
Article: jacobi, Proposition C.2.
Proof: the original a/a_0 tends to one and 1/y tends to zero. Reassociate the same original quotient. -/
theorem midpointValue_negative_scaled (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => midpointValue a ha (shiftedNegativeEnergy a y)/
      ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2))) atTop (𝓝 0) := by
  -- The actual reference-normalized value stays bounded while the additional genuine factor 1/y tends to zero.
  have hi := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero : Tendsto (fun y:ℝ => y⁻¹) atTop (𝓝 0))
  have h := (transformed_midpoint_negative_limit a ha).mul hi
  simp only [Complex.ofReal_zero,mul_zero] at h
  apply h.congr'
  filter_upwards [] with y
  change (midpointValue a ha (shiftedNegativeEnergy a y)/solution a (shiftedNegativeEnergy a y) (1/2))*(y⁻¹:ℝ)=_
  rw [Complex.ofReal_inv]
  ring

/-- The leading negative-axis coefficient of each actual original separated characteristic is minus its genuine first midpoint value.
Use: midpoint_first_values_product_zero combines both actual characteristic limits with the proved original global product factorization.
Article: jacobi, Proposition C.2.
Proof: divide the original determinant by y*a_0. Its actual value term tends to zero and its actual derivative term tends to one, with unchanged original first-state coefficients. -/
theorem separatedCharacteristic_negative_leading (a : ℝ) (ha : -1<a) (p : Fin 2) :
    Tendsto (fun y:ℝ => separatedCharacteristic a ha p (shiftedNegativeEnergy a y)/
      ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2))) atTop
      (𝓝 (-midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ))) := by
  -- The lower-order actual value vanishes in this scale, while the actual slope retains its proved unit reference leading term.
  have h := ((midpointValue_negative_scaled a ha).mul_const
    (midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ))).sub
      ((midpointSlope_negative_leading a ha).mul_const
        (midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)))
  simp only [zero_mul,one_mul,zero_sub] at h
  apply h.congr'
  filter_upwards [] with y
  dsimp only [separatedCharacteristic,shiftedNegativeEnergy]
  ring

/-- Both actual reference midpoint coordinates and the true reference characteristic are nonzero on a sufficiently negative original energy tail.
Use: characteristicSigma_negative_scaled cancels only genuine nonzero original factors in the normalized characteristic comparison.
Article: jacobi, Proposition C.2.
Proof: the proved normalized original reference slope tends to one, hence is eventually nonzero. Its numerator and denominator are therefore nonzero. The exact original reference characteristic product excludes a zero of Delta_tau there as well. -/
theorem reference_negative_midpoint_nonzero (a : ℝ) (ha : -1<a) :
    ∀ᶠ y:ℝ in atTop,solution a (shiftedNegativeEnergy a y) (1/2)≠0 ∧
      solutionSlope a (shiftedNegativeEnergy a y) (1/2)≠0 ∧
      characteristicTau a (shiftedNegativeEnergy a y)≠0 := by
  -- Eventual nonvanishing is deduced from the already proved actual leading limit before any normalization is cancelled.
  filter_upwards [(reference_midpointSlope_negative_leading a ha).eventually_ne one_ne_zero] with y hy
  obtain ⟨hb,hden⟩ := div_ne_zero_iff.mp hy
  have hf := (mul_ne_zero_iff.mp hden).2
  refine ⟨hf,hb,?_⟩
  intro hT
  have h := solution_midpoint_product ha (shiftedNegativeEnergy a y)
  rw [hT,mul_zero] at h
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℂ)≠0) hf) hb) h

/-- The actual original Bessel characteristic divided by y*a_0^2 has its exact reference normalization 2/kappa.
Use: the boundary-class assignment determines the true separated-product scalar using the original negative-energy normalization.
Article: jacobi, Proposition C.2.
Proof: use 2*a_0*b_0=kappa*Delta_tau, the original b_0/(y*a_0) limit one and the genuine relative Delta_sigma/Delta_tau limit one. Every cancellation occurs on the independently proved nonzero negative tail. -/
theorem characteristicSigma_negative_reference_limit (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => characteristicSigma a (shiftedNegativeEnergy a y)/
      ((y:ℂ)*(solution a (shiftedNegativeEnergy a y) (1/2))^2)) atTop
      (𝓝 (2/((2*Real.pi^2*normConstant a:ℝ):ℂ))) := by
  -- The scalar is the original kappa from the exact reference product, rather than a new characteristic normalization.
  let κ : ℂ := ((2*Real.pi^2*normConstant a:ℝ):ℂ)
  have hk : κ≠0 := Complex.ofReal_ne_zero.mpr (by positivity [normConstant_pos ha])
  have hr : Tendsto (fun y:ℝ => characteristicSigma a (shiftedNegativeEnergy a y)/
      characteristicTau a (shiftedNegativeEnergy a y)) atTop (𝓝 1) := by
    simpa only [shiftedNegativeEnergy,inv_div,inv_one] using (characteristic_negative_ratio ha).inv₀ one_ne_zero
  have h := ((reference_midpointSlope_negative_leading a ha).mul hr).const_mul (2/κ)
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [reference_negative_midpoint_nonzero a ha,eventually_gt_atTop (0:ℝ)] with y hy hyp
  obtain ⟨hf,_,hT⟩ := hy
  have hprod := solution_midpoint_product ha (shiftedNegativeEnergy a y)
  change 2*solution a (shiftedNegativeEnergy a y) (1/2)*solutionSlope a (shiftedNegativeEnergy a y) (1/2)=
    κ*characteristicTau a (shiftedNegativeEnergy a y) at hprod
  dsimp only [Function.comp_apply,shiftedNegativeEnergy] at hprod hf hT ⊢
  field_simp [hk,hf,hT,Complex.ofReal_ne_zero.mpr hyp.ne']
  linear_combination (characteristicSigma a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ))*hprod

/-- The actual original Bessel characteristic divided by y^2*a_0^2 tends to zero on the unchanged shifted negative-energy path.
Use: midpoint_first_values_product_zero forces a genuine Dirichlet separated class from the actual constant full-product factorization.
Article: jacobi, Proposition C.2.
Proof: multiply the proved exact original Delta_sigma/(y*a_0^2) limit by the actual reciprocal-frequency limit zero. -/
theorem characteristicSigma_negative_scaled (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => characteristicSigma a (shiftedNegativeEnergy a y)/
      ((y:ℂ)^2*(solution a (shiftedNegativeEnergy a y) (1/2))^2)) atTop (𝓝 0) := by
  -- The actual full characteristic has only one frequency factor in this normalization, so the additional inverse-frequency factor forces a zero limit.
  have hi := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero : Tendsto (fun y:ℝ => y⁻¹) atTop (𝓝 0))
  have h := (characteristicSigma_negative_reference_limit a ha).mul hi
  simp only [Complex.ofReal_zero,mul_zero] at h
  apply h.congr'
  filter_upwards [] with y
  dsimp only [Function.comp_apply]
  rw [Complex.ofReal_inv]
  ring

/-- At least one actual original first parity midpoint value is zero.
Use: the exact boundary-class assignment of Proposition C.2 starts with a genuine Dirichlet class rather than presupposing either target midpoint condition.
Article: jacobi, Proposition C.2.
Proof: dividing both original separated characteristics by y*a_0 gives the product limit A_0*A_1. The proved global original product factorization and the actual full characteristic growth give the same limit zero. Uniqueness of limits forces A_0*A_1=0. -/
theorem midpoint_first_values_product_zero (a : ℝ) (ha : -1<a) :
    midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 0 0):ℂ)=0 ∨
      midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 1 0):ℂ)=0 := by
  -- The entire factor is already proved constant; a hypothetical zero-free varying normalization cannot enter this comparison.
  obtain ⟨C,_,hC⟩ := separatedProduct_factorization a ha
  have hprod := (separatedCharacteristic_negative_leading a ha 0).mul
    (separatedCharacteristic_negative_leading a ha 1)
  simp only [neg_mul_neg] at hprod
  have hzero := (characteristicSigma_negative_scaled a ha).const_mul C
  simp only [mul_zero] at hzero
  have hsame : (fun y:ℝ => (separatedCharacteristic a ha 0 (shiftedNegativeEnergy a y)/
      ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2)))*
      (separatedCharacteristic a ha 1 (shiftedNegativeEnergy a y)/
      ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2))))=
      (fun y => C*(characteristicSigma a (shiftedNegativeEnergy a y)/
        ((y:ℂ)^2*(solution a (shiftedNegativeEnergy a y) (1/2))^2))) := by
    funext y
    rw [div_mul_div_comm,hC]
    ring
  rw [hsame] at hprod
  exact mul_eq_zero.mp (tendsto_nhds_unique hprod hzero)

end
end jacobi.GelfandLevitan
