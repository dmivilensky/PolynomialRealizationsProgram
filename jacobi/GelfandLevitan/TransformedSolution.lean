import jacobi.GelfandLevitan.IntegralEquation
import jacobi.Reference.HalfSolution

/-!
Article: jacobi, Theorem 2.1.
The actual GL kernel defines the transformed solution at every complex
energy. Its source row integral is a bounded functional applied to the
entire continuous-function reference solution. The resulting u is entire
in energy, has the literal triangular transformation integral and takes
real values at every real energy. The transformed differential equation
requires the separate differentiability argument for K.
Use: defines the literal transformed solution and proves its entire complex-energy dependence without differentiating an arbitrary square root.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The bounded source functional combining physical point evaluation with the actual inverse GL row integral.
Use: defines the literal transformed solution and proves its entire complex-energy dependence without differentiating an arbitrary square root.
Article: jacobi, Theorem 2.1.
-/
def transformationFunctional (a : ℝ) (ha : -1<a) (t : HalfInterval) : C(Interval,ℂ) →L[ℂ] ℂ :=
  ContinuousMap.evalCLM ℂ (halfInclusion t)+coefficientFunctional (solutionRow a ha t:Space)

/-- The actual transformed solution constructed from the article's reference data and the proved inverse GL row.
Use: supplies the source u(t,z) in the continuum profiles and the subsequent transformed differential equation and target spectral realization.
Article: jacobi, Proposition 2.2.
-/
def transformedSolution (a : ℝ) (ha : -1<a) (t : HalfInterval) (z : ℂ) : ℂ :=
  transformationFunctional a ha t (halfSolution a ha z)

/-- The actual transformed solution is entire in the original complex energy at every physical point, including zero.
Use: the source spectral profiles and subsequent characteristic arguments refer to the constructed solution at every energy, including the frequency branch point.
Article: jacobi, Proposition C.2.
Proof: compose the proved entire reference solution in its genuine continuous-function norm with the actual bounded complex-linear evaluation-plus-GL-integral functional. -/
theorem transformedSolution_analytic (a : ℝ) (ha : -1<a) (t : HalfInterval) (z : ℂ) :
    AnalyticAt ℂ (transformedSolution a ha t) z :=
  ((transformationFunctional a ha t).analyticAt _).comp (halfSolution_analytic a ha z)

/-- The transformed solution is exactly the original reference value plus the original inverse-row integral functional.
Use: identifies the entire functional construction with the literal source spatial transformation integral and its real-energy values.
Article: jacobi, Theorem 2.1.
Proof: expand the actual evaluation-plus-integral functional. The genuine reference function-space evaluation equals f at the physical coordinate, whose clamp is unchanged because t<=1/2. -/
theorem transformedSolution_reference_form (a : ℝ) (ha : -1<a) (t : HalfInterval) (z : ℂ) :
    transformedSolution a ha t z=solution a z (t:ℝ)+
      coefficientFunctional (solutionRow a ha t:Space) (halfSolution a ha z) := by
  rw [transformedSolution,transformationFunctional,add_apply]
  change halfSolution a ha z (halfInclusion t)+_=solution a z (t:ℝ)+_
  rw [halfSolution_apply]
  change solution a z (min (t:ℝ) (1/2))+_=solution a z (t:ℝ)+_
  rw [min_eq_left t.property.2]

/-- The actual source integrand defining the GL correction to u is genuinely Bochner integrable for every complex energy.
Use: the entire transformed solution uses a true spatial integral, with all subsequent linearity and norm estimates justified.
Article: jacobi, Proposition C.4.
Proof: the actual inverse solution row is an original L2 input, hence L1; the original continuous reference solution is bounded on the compact physical domain. Apply the already proved source coefficient integrability theorem. -/
theorem transformedSolution_integrable (a : ℝ) (ha : -1<a) (t : HalfInterval) (z : ℂ) :
    Integrable (fun r:Interval => ((solutionRow a ha t:Space) r:ℂ)*halfSolution a ha z r) :=
  coefficient_integrable (solutionRow a ha t:Space) (halfSolution a ha z)

/-- The entire transformed solution has exactly the article's literal physical-prefix transformation integral with the actual constructed K.
Use: identifies the original analytic u with the source GL solution used in continuum persymmetry and the target Schrodinger equation.
Article: jacobi, Proposition C.2.
Proof: the actual inverse row has the proved physical indicator times
K as its genuine representative. Substitute that identity in the true
complex spatial integral, use the original function-space evaluation
identity, and restrict its actual indicator integral to the source prefix. -/
theorem transformedSolution_integral (a : ℝ) (ha : -1<a) (t : HalfInterval) (z : ℂ) :
    transformedSolution a ha t z=solution a z (t:ℝ)+
      ∫ r:Interval in prefixSet (t:ℝ),
        (transformationKernel a ha t (halfClamp r):ℂ)*solution a z (halfTime r) := by
  -- The original row equality is used only almost everywhere, exactly as required for the actual Lebesgue integral.
  rw [transformedSolution_reference_form]
  congr 1
  change (∫ r:Interval,((solutionRow a ha t:Space) r:ℂ)*halfSolution a ha z r)=_
  rw [← integral_indicator (prefixSet_measurable (t:ℝ))]
  apply integral_congr_ae
  filter_upwards [solutionRow_representative a ha t] with r hr
  rw [hr]
  by_cases hp : r∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp,indicator_of_mem hp,halfSolution_apply]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,Complex.ofReal_zero,zero_mul]

/-- The actual transformed solution at a real energy is the complex inclusion of its true real reference-plus-coefficient expression.
Use: all source squared spectral profiles and real target equations use actual real values of u, without a branch-dependent reality premise.
Article: jacobi, Theorem 2.1.
Proof: choose the genuine square-root frequency of the prescribed real
energy. The original integral functional is its true coefficient
transform, whose proved real-energy identity is the real coefficient.
The reference value is already proved real; complex inclusion preserves
their actual sum. -/
theorem transformedSolution_real (a : ℝ) (ha : -1<a) (t : HalfInterval) (E : ℝ) :
    transformedSolution a ha t (E:ℂ)=
      (realSolution a E (t:ℝ)+realCoefficient a (solutionRow a ha t:Space) E:ℝ) := by
  -- Both terms are the actual source expressions even when the original real energy itself is negative.
  rw [transformedSolution_reference_form]
  let omega := Complex.sqrt ((E:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hv : coefficientFunctional (solutionRow a ha t:Space) (halfSolution a ha (E:ℂ))=
      (realCoefficient a (solutionRow a ha t:Space) E:ℂ) := by
    change coefficientFunctional (solutionRow a ha t:Space) (halfWave a ha omega)=_
    rw [← coefficientTransform_eq a ha]
    exact coefficientTransform_at_energy a _ (frequency_square _)
  rw [hv,← realSolution_cast,Complex.ofReal_add]

end
end jacobi.GelfandLevitan
