import jacobi.GelfandLevitan.MidpointRobin
import jacobi.GelfandLevitan.MidpointNegativeFine
import jacobi.Reference.RelativeNegativeRate

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual remaining boundary parameter is zero. The proved original
midpoint diagonal zero improves a/a_0 enough to compare the exactly
normalized mixed characteristic product with the actual relative
spectral product. Hence the other class is exactly Neumann, all a,b
zeros have their prescribed parity and multiplicity, and the printed
2*a*b=kappa*Delta_sigma identity holds for the original functions.
Use: midpointRobinParameter_zero applies it to the independently proved original characteristic product and true nonzero negative-axis reference values.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Exact quotient algebra expressing a mixed characteristic product in terms of its actual reference-normalized errors.
Use: midpointRobinParameter_zero applies it to the independently proved original characteristic product and true nonzero negative-axis reference values.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: elementary complex quotient algebra.
Proof: clear the three stated genuine nonzero denominators and use the given exact mixed-product equality. -/
private theorem robin_comparison_algebra {a u b v S D l y : ℂ}
    (hy : y≠0) (hu : u≠0) (hS : S≠0)
    (h : D*a*(b-l*a)=S*u*v) :
    (D/S)*(a/u)*(b/u-v/u)+(v/(y*u))*
      ((D/S)*(y*(a/u-1))+y*(D/S-1))=(D/S)*l*(a/u)^2 := by
  field_simp [hy,hu,hS]
  linear_combination h

/-- The actual original non-Dirichlet boundary parameter is zero, so its genuine boundary class is exactly Neumann.
Use: midpointSlope_zero_iff, midpoint_neumann_at_spectrum and midpoint_characteristic_product complete the original boundary and exact characteristic assertions without a residual Robin premise.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: use the genuine normalized errors A=a/a_0, U=(b-b_0)/a_0, R=Delta_tau/Delta_sigma and Q=b_0/(y*a_0). The actual diagonal zero and endpoint Laplace argument prove y*(A-1) to zero and U to zero. The exact original relative product proves y*(R-1) to zero, while A,R,Q tend to one. The original mixed characteristic product gives R*A*U+Q*(R*y*(A-1)+y*(R-1))=R*lambda*A^2. Its two genuine limits are zero and lambda, forcing lambda=0. -/
theorem midpointRobinParameter_zero (a : ℝ) (ha : -1<a) : midpointRobinParameter a ha=0 := by
  -- Every normalized error is for the actual original midpoint functions; all three fine limits have been proved independently.
  let E := shiftedNegativeEnergy a
  let A := fun y:ℝ => midpointValue a ha (E y)/solution a (E y) (1/2)
  let R := fun y:ℝ => characteristicTau a (E y)/characteristicSigma a (E y)
  let U := fun y:ℝ => midpointSlope a ha (E y)/solution a (E y) (1/2)-
    solutionSlope a (E y) (1/2)/solution a (E y) (1/2)
  let Q := fun y:ℝ => solutionSlope a (E y) (1/2)/((y:ℂ)*solution a (E y) (1/2))
  have hA : Tendsto A atTop (𝓝 1) := transformed_midpoint_negative_limit a ha
  have hR : Tendsto R atTop (𝓝 1) := characteristic_negative_ratio ha
  have hU : Tendsto U atTop (𝓝 0) := midpointSlope_negative_difference a ha
  have hQ : Tendsto Q atTop (𝓝 1) := reference_midpointSlope_negative_leading a ha
  have hAE : Tendsto (fun y:ℝ => (y:ℂ)*(A y-1)) atTop (𝓝 0) := midpointValue_negative_scaled_error a ha
  have hRE : Tendsto (fun y:ℝ => (y:ℂ)*(R y-1)) atTop (𝓝 0) := relative_characteristic_negative_scaled_error a ha
  have hL : Tendsto (fun y:ℝ => R y*A y*U y+
      Q y*(R y*((y:ℂ)*(A y-1))+(y:ℂ)*(R y-1))) atTop (𝓝 0) := by
    simpa using ((hR.mul hA).mul hU).add (hQ.mul ((hR.mul hAE).add hRE))
  have hRight : Tendsto (fun y:ℝ => R y*midpointRobinParameter a ha*(A y)^2)
      atTop (𝓝 (midpointRobinParameter a ha)) := by
    simpa only [mul_one,one_mul,one_pow] using (hR.mul_const (midpointRobinParameter a ha)).mul (hA.pow 2)
  have he : (fun y:ℝ => R y*A y*U y+Q y*(R y*((y:ℂ)*(A y-1))+(y:ℂ)*(R y-1)))=ᶠ[atTop]
      (fun y:ℝ => R y*midpointRobinParameter a ha*(A y)^2) := by
    -- The exact original mixed product and reference product are combined before their denominators are cancelled.
    filter_upwards [reference_negative_midpoint_nonzero a ha,eventually_gt_atTop (0:ℝ)] with y hy hyp
    have hmix := midpoint_robin_product a ha (E y)
    have href := solution_midpoint_product ha (E y)
    have hcross : characteristicTau a (E y)*midpointValue a ha (E y)*
        (midpointSlope a ha (E y)-midpointRobinParameter a ha*midpointValue a ha (E y))=
        characteristicSigma a (E y)*solution a (E y) (1/2)*solutionSlope a (E y) (1/2) := by
      unfold midpointRobinCharacteristic at hmix
      apply mul_left_cancel₀ (by norm_num : (2:ℂ)≠0)
      linear_combination (characteristicTau a (E y))*hmix-(characteristicSigma a (E y))*href
    exact robin_comparison_algebra (Complex.ofReal_ne_zero.mpr hyp.ne') hy.1
      (characteristicSigma_shifted_negative_ne_zero a ha y) hcross
  have hz := tendsto_nhds_unique (hL.congr' he) hRight
  exact hz.symm

/-- Every original odd one-based target spectral state satisfies its exact Neumann midpoint derivative condition.
Use: the actual even reflected target waves glue with their genuine first derivatives at the physical midpoint.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine original Robin characteristic has exactly this spectral zero set, and its independently determined actual parameter is now proved zero. -/
theorem midpoint_neumann_at_spectrum (a : ℝ) (ha : -1<a) (k : ℕ) :
    midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex 0 k):ℂ)=0 := by
  have h := (midpointRobinCharacteristic_zero_iff a ha _).mpr ⟨k,rfl⟩
  simpa only [midpointRobinCharacteristic,midpointRobinParameter_zero,zero_mul,sub_zero] using h

/-- The actual original derivative characteristic has exactly the original odd one-based target spectral zeros, with no additional complex zeros.
Use: the exact Neumann class and full reflected differential realization retain the complete original target spectrum.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the already exhaustive actual Robin zero set becomes precisely b's zero set after the genuine parameter is proved zero. -/
theorem midpointSlope_zero_iff (a : ℝ) (ha : -1<a) (z : ℂ) :
    midpointSlope a ha z=0 ↔ ∃ k:ℕ,z=(jacobi.Bessel.sigma a ha (parityIndex 0 k):ℂ) := by
  simpa only [midpointRobinCharacteristic,midpointRobinParameter_zero,zero_mul,sub_zero] using
    midpointRobinCharacteristic_zero_iff a ha z

/-- Every genuine complex zero of the actual original Neumann derivative characteristic is simple in energy.
Use: completes the multiplicity assertion for both original midpoint characteristics in the exact target realization.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: its separated characteristic is a nonzero original first-value multiple of b. The proved simple separated zero excludes a vanishing genuine derivative of b. -/
theorem midpointSlope_simple (a : ℝ) (ha : -1<a) {z : ℂ} (hz : midpointSlope a ha z=0) :
    deriv (midpointSlope a ha) z≠0 := by
  have hS : separatedCharacteristic a ha 0 z=0 := by
    rw [separatedCharacteristic,midpoint_neumann_at_spectrum,hz,mul_zero,zero_mul,sub_self]
  have hd := separatedCharacteristic_simple a ha 0 hS
  rw [separatedCharacteristic_derivative,midpoint_neumann_at_spectrum,mul_zero,zero_sub] at hd
  intro h
  exact hd (by rw [h,zero_mul,neg_zero])

/-- The genuine original midpoint value and actual derivative characteristics have exactly the printed full Bessel characteristic product at every complex energy.
Use: supplies the exact normalized characteristic assertion of general Proposition C.2 and the subsequent full target Green and differential realization.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the independently normalized actual mixed characteristic identity becomes the printed original product after the genuine residual boundary parameter has been proved zero. -/
theorem midpoint_characteristic_product (a : ℝ) (ha : -1<a) (z : ℂ) :
    2*midpointValue a ha z*midpointSlope a ha z=
      ((2*Real.pi^2*normConstant a:ℝ):ℂ)*characteristicSigma a z := by
  simpa only [midpointRobinCharacteristic,midpointRobinParameter_zero,zero_mul,sub_zero] using
    midpoint_robin_product a ha z

end
end jacobi.GelfandLevitan
