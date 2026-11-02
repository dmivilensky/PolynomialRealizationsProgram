import jacobi.GelfandLevitan.HalfContinuousPairing
import jacobi.GelfandLevitan.ContinuousTransformation

/-!
Article: jacobi, Proposition C.2.
The full Green identity is written as an actual complex coefficient
functional against a real transformed Hilbert vector. Its energy
derivative at a spectral point equals the genuine positive squared
norm. This is the simple-zero mechanism for the separated characteristics.
Use: complex_hilbert_green and the characteristic-zero argument use the same true coefficient functionals and actual transformed bases.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- Pairing the actual real transformed Hilbert vector with a complex-energy wave gives the original complex half-interval product integral.
Use: complex_hilbert_green and the characteristic-zero argument use the same true coefficient functionals and actual transformed bases.
Article: jacobi, Proposition C.2.
Proof: insert the genuine zero-extended representative of the real transformed vector, use its proved reality, and transfer the true prefix integral to the physical real half interval. -/
theorem transformedVector_complex_integral (a : ℝ) (ha : -1<a) (E : ℝ) (z : ℂ) :
    coefficientFunctional (transformedVector a ha E:Space) (transformedWaveMap a ha z)=
      ∫ r in (0:ℝ)..(1/2:ℝ),transformedSolution a ha (halfParameterClamp r) z*
        transformedSolution a ha (halfParameterClamp r) (E:ℂ) := by
  -- The actual L2 representative is substituted only inside the integral; the endpoint values come from the original continuous solution.
  change (∫ r:Interval,((transformedVector a ha E:Space) r:ℂ)*transformedWaveMap a ha z r)=_
  rw [← prefix_integral (fun r => transformedSolution a ha (halfParameterClamp r) z*
    transformedSolution a ha (halfParameterClamp r) (E:ℂ)) (by norm_num : (1/2:ℝ)∈Icc (0:ℝ) 1),
    ← integral_indicator (prefixSet_measurable (1/2))]
  apply integral_congr_ae
  filter_upwards [transformedVector_ae a ha E] with r hr
  rw [hr,transformedWaveMap_apply]
  by_cases hp : r∈prefixSet (1/2)
  · rw [indicator_of_mem hp,indicator_of_mem hp,halfParameterClamp_unit]
    change ((transformedSolution a ha (halfClamp r) (E:ℂ)).re:ℂ)*
      transformedSolution a ha (halfClamp r) z=_
    rw [transformedSolution_cast_re]
    ring
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,Complex.ofReal_zero,zero_mul]

/-- The original Green identity at arbitrary complex energy uses the actual complex pairing with a genuine real transformed vector.
Use: separatedCharacteristic_zero_iff excludes additional complex zeros by completeness of the actual transformed parity basis.
Article: jacobi, Proposition C.2.
Proof: rewrite the genuine original product integral in the proved full midpoint Green identity using its actual Hilbert-functional representation. -/
theorem complex_hilbert_green (a : ℝ) (ha : -1<a) (z : ℂ) (E : ℝ) :
    (z-(E:ℂ))*coefficientFunctional (transformedVector a ha E:Space) (transformedWaveMap a ha z)=
      midpointValue a ha z*midpointSlope a ha (E:ℂ)-
        midpointSlope a ha z*midpointValue a ha (E:ℂ) := by
  rw [transformedVector_complex_integral]
  exact midpoint_green_identity a ha z (E:ℂ)

/-- Differentiation of the genuine Green determinant at a real spectral energy gives the actual squared norm of its original transformed solution.
Use: separatedCharacteristic_simple proves simplicity from the independently proved positive norm of the actual basis vector.
Article: jacobi, Proposition C.2.
Proof: the true complex coefficient functional applied to u is analytic in the uniform spatial norm. Differentiate (z-E) times this same genuine pairing at E and use the original global Green equality. Its pairing at E is the independently identified real Hilbert norm. -/
theorem midpoint_green_derivative (a : ℝ) (ha : -1<a) (E : ℝ) :
    deriv (midpointValue a ha) (E:ℂ)*midpointSlope a ha (E:ℂ)-
      deriv (midpointSlope a ha) (E:ℂ)*midpointValue a ha (E:ℂ)=
        (inner ℝ (transformedVector a ha E) (transformedVector a ha E):ℂ) := by
  -- The derivative is in the original complex energy, and the normalization is the unchanged physical half-interval norm.
  let C := fun z => coefficientFunctional (transformedVector a ha E:Space) (transformedWaveMap a ha z)
  have hC := (((coefficientFunctional (transformedVector a ha E:Space)).analyticAt _).comp
    (transformedWaveMap_analytic a ha (E:ℂ))).differentiableAt.hasDerivAt
  have hL := ((hasDerivAt_id (E:ℂ)).sub_const (E:ℂ)).mul hC
  have hR := ((midpointValue_analytic a ha (E:ℂ)).differentiableAt.hasDerivAt.mul_const
    (midpointSlope a ha (E:ℂ))).sub
      ((midpointSlope_analytic a ha (E:ℂ)).differentiableAt.hasDerivAt.mul_const (midpointValue a ha (E:ℂ)))
  have he : (fun z => (z-(E:ℂ))*C z)=fun z =>
      midpointValue a ha z*midpointSlope a ha (E:ℂ)-midpointSlope a ha z*midpointValue a ha (E:ℂ) :=
    funext (fun z => complex_hilbert_green a ha z E)
  change HasDerivAt (fun z => (z-(E:ℂ))*C z) _ (E:ℂ) at hL
  rw [he] at hL
  have hd := hR.unique hL
  simp only [id_eq,sub_self,zero_mul,one_mul,add_zero] at hd
  rw [hd]
  change coefficientFunctional _ (transformedWaveMap a ha (E:ℂ))=_
  rw [transformedVector_complex_integral,← transformedVector_inner_integral]

end
end jacobi.GelfandLevitan
