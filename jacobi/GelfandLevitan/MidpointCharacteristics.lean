import jacobi.GelfandLevitan.TransformedSmoothness
import jacobi.GelfandLevitan.NegativeComparison

/-!
Article: jacobi, Proposition C.2.
The original midpoint characteristics are the actual value of u and
its proved genuine one-sided spatial derivative. Both are entire in
the original energy and real on the real axis. Their definitions make
no assumption about zeros, boundary closure or the target operator.
Use: the general Proposition C.2 must subsequently identify its zeros and its exact normalized product with the original derivative characteristic.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope transformationKernel

/-- The actual original midpoint value characteristic of the constructed transformed solution.
Use: the general Proposition C.2 must subsequently identify its zeros and its exact normalized product with the original derivative characteristic.
Article: jacobi, Proposition C.2.
-/
def midpointValue (a : ℝ) (ha : -1<a) (z : ℂ) : ℂ := transformedSolution a ha halfMidpoint z

/-- The actual original midpoint derivative characteristic, using the proved genuine spatial derivative of u on the fixed quarter-to-midpoint strip.
Use: midpointSlope_hasDerivWithinAt identifies it with the actual left derivative of u, while midpointSlope_analytic proves its true entire energy dependence.
Article: jacobi, Proposition C.2.
-/
def midpointSlope (a : ℝ) (ha : -1<a) (z : ℂ) : ℂ :=
  transformedSlopeRows ha (d := 1/4) (by norm_num) z ⟨1/2,by norm_num⟩

/-- The genuine original midpoint derivative row vector in the unchanged source L2 space.
Use: midpointSlope_reference exhibits the actual b as its genuine original reference slope, diagonal term and bounded source coefficient functional, proving entire energy dependence.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def midpointDerivativeVector (a : ℝ) (ha : -1<a) : Space :=
  candidateVector halfMidpoint (derivativeCandidateRows ha (d := 1/4) (by norm_num) ⟨1/2,by norm_num⟩)

/-- The original derivative characteristic is the actual midpoint left derivative of the original transformed solution.
Use: subsequent boundary and target-operator statements use the genuine spatial b rather than an independently postulated entire function.
Article: jacobi, Proposition C.2.
Proof: specialize the proved actual transformed-solution derivative to the original midpoint and the genuine nondegenerate positive quarter strip. -/
theorem midpointSlope_hasDerivWithinAt (a : ℝ) (ha : -1<a) (z : ℂ) :
    HasDerivWithinAt (fun t : ℝ => transformedSolution a ha (halfParameterClamp t) z)
      (midpointSlope a ha z) (Icc (1/4:ℝ) (1/2)) (1/2) :=
  transformedSolution_hasDerivWithinAt ha (by norm_num) z halfMidpoint (by norm_num [halfMidpoint])

/-- The actual original midpoint derivative characteristic is its genuine reference slope plus the original bounded correction functional and diagonal term.
Use: midpointSlope_analytic proves true entire energy dependence directly from the already proved original solution and slope analyticity.
Article: jacobi, Proposition C.2.
Proof: evaluate the original actual derivative formula at the midpoint. Its genuine prefix integral functional is coefficientFunctional of the true midpoint derivative vector; scalar reassociation gives the printed order. -/
theorem midpointSlope_reference (a : ℝ) (ha : -1<a) (z : ℂ) :
    midpointSlope a ha z=solutionSlope a z (1/2)+
      (kernelDiagonal a ha halfMidpoint:ℂ)*solution a z (1/2)+
      coefficientFunctional (midpointDerivativeVector a ha) (halfSolution a ha z) := by
  change solutionSlope a z (1/2)+
    (coefficientFunctional (midpointDerivativeVector a ha) (halfSolution a ha z)+
      (kernelDiagonal a ha halfMidpoint:ℂ)*halfSolution a ha z (halfInclusion halfMidpoint))=_
  rw [halfSolution_apply]
  change solutionSlope a z (1/2)+(coefficientFunctional _ _+_ * solution a z (min (1/2) (1/2)))=_
  rw [min_self]
  abel

/-- The original midpoint value characteristic is entire in its genuine complex energy.
Use: the original midpoint characteristic has the analytic hypothesis required by the subsequent actual zero and canonical-product arguments in Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: specialize the independently proved actual transformed-solution analyticity to its unchanged midpoint. -/
theorem midpointValue_analytic (a : ℝ) (ha : -1<a) (z : ℂ) : AnalyticAt ℂ (midpointValue a ha) z :=
  transformedSolution_analytic a ha halfMidpoint z

/-- The original midpoint derivative characteristic is entire in its genuine complex energy, including the frequency branch point.
Use: supplies the actual analytic b needed by the general boundary and normalized characteristic-product assertions of Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: its actual reference slope is entire, its actual midpoint reference value is entire and multiplied by a fixed original real diagonal, and the original genuine coefficient functional preserves the entire continuous-function reference solution. -/
theorem midpointSlope_analytic (a : ℝ) (ha : -1<a) (z : ℂ) : AnalyticAt ℂ (midpointSlope a ha) z := by
  have he : midpointSlope a ha=fun w : ℂ => solutionSlope a w (1/2)+
      (kernelDiagonal a ha halfMidpoint:ℂ)*solution a w (1/2)+
      coefficientFunctional (midpointDerivativeVector a ha) (halfSolution a ha w) :=
    funext (midpointSlope_reference a ha)
  rw [he]
  exact ((solutionSlope_energy_analytic ha (by norm_num) z).add
    (analyticAt_const.mul (solution_energy_analytic_half ha (by norm_num) z))).add
      (((coefficientFunctional (midpointDerivativeVector a ha)).analyticAt _).comp (halfSolution_analytic a ha z))

/-- The genuine source coefficient integral of the original continuous-function reference solution is real at every real energy.
Use: midpointSlope_real proves reality of the original derivative characteristic from its independently identified actual spatial derivative formula.
Article: jacobi, Proposition C.2.
Proof: the actual complex square-root frequency has precisely the prescribed real energy. The proved original coefficient-transform reality identity identifies this same original integral with its real coefficient. -/
theorem coefficient_halfSolution_real (a : ℝ) (ha : -1<a) (v : Space) (E : ℝ) :
    coefficientFunctional v (halfSolution a ha (E:ℂ))=(realCoefficient a v E:ℂ) := by
  let omega := Complex.sqrt ((E:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ))
  change coefficientFunctional v (halfWave a ha omega)=_
  rw [← coefficientTransform_eq a ha]
  exact coefficientTransform_at_energy a v (frequency_square _)

/-- The original midpoint value characteristic takes real values at every real energy, with its actual source normalization unchanged.
Use: the boundary-class and negative-energy arguments in Proposition C.2 apply to this same original real characteristic.
Article: jacobi, Proposition C.2.
Proof: specialize the proved actual original transformed-solution reality identity to the physical midpoint. -/
theorem midpointValue_real (a : ℝ) (ha : -1<a) (E : ℝ) :
    midpointValue a ha (E:ℂ)=(realSolution a E (1/2)+realCoefficient a (solutionRow a ha halfMidpoint:Space) E:ℝ) :=
  transformedSolution_real a ha halfMidpoint E

/-- The original midpoint derivative characteristic takes real values at every real energy and is the genuine displayed original real slope-plus-integral expression.
Use: fixes the real b in the boundary-class, negative-energy and characteristic-product arguments of the general target-operator Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: use the exact original midpoint derivative formula. Its genuine reference slope and reference solution are real, and its actual original coefficient integral has the independently proved real-energy value. -/
theorem midpointSlope_real (a : ℝ) (ha : -1<a) (E : ℝ) :
    midpointSlope a ha (E:ℂ)=(realSlope a E (1/2)+kernelDiagonal a ha halfMidpoint*realSolution a E (1/2)+
      realCoefficient a (midpointDerivativeVector a ha) E:ℝ) := by
  rw [midpointSlope_reference,coefficient_halfSolution_real]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,realSolution_cast,realSlope,
    solutionSlope_real a E (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)]

end
end jacobi.GelfandLevitan
