import jacobi.GelfandLevitan.FiniteIntegralEquation
import jacobi.GelfandLevitan.MidpointCharacteristics

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite GL solution gives the genuine finite transformed
solution with its original physical K^(N) integral. Its diagonal and
transformed solution converge uniformly to the original w and u.
Energy analyticity and reality concern the same original finite data.
Use: finiteKernelDiagonal_uniform_limit supplies the original diagonal limit when the genuine finite quasi-derivative identities are integrated and passed to the original u.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution transformationKernel transformedSolution

/-- The actual finite original GL diagonal.
Use: finiteKernelDiagonal_uniform_limit supplies the original diagonal limit when the genuine finite quasi-derivative identities are integrated and passed to the original u.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteKernelDiagonal (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) : ℝ :=
  finiteTransformationKernel a ha N t t

/-- The original finite transformed solution from the genuine finite inverse row at each original complex energy.
Use: finiteTransformedSolution_integral identifies this same source solution with its literal original K^(N) transformation integral, before its genuine finite differential identity is used.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteTransformedSolution (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (z : ℂ) : ℂ :=
  solution a z t+coefficientInput (halfSolution a ha z) (finiteSolutionRow a ha N t:Space)

/-- The actual original finite transformed solution has exactly its genuine original finite K transformation integral in the original physical measure.
Use: the finite differential-equation calculation and the uniform limit refer to the same original u^(N), with no transformation-kernel identification assumed.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine finite inverse row is the proved original physical-prefix representative of K^(N). Substitute this actual representative in its true coefficient integral and apply the community indicator-integral identity. -/
theorem finiteTransformedSolution_integral (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (z : ℂ)
    (hu : IsUnit (finiteCompressedPositive a ha N t)) :
    finiteTransformedSolution a ha N t z=solution a z t+
      ∫ r : Interval in prefixSet (t:ℝ),(finiteTransformationKernel a ha N t (halfClamp r):ℂ)*solution a z (halfTime r) := by
  -- The original physical zero extension is substituted only almost everywhere in the unchanged original Lebesgue integral.
  rw [finiteTransformedSolution]
  congr 1
  change (∫ r : Interval,((finiteSolutionRow a ha N t:Space) r:ℂ)*halfSolution a ha z r)=_
  rw [← integral_indicator (prefixSet_measurable (t:ℝ))]
  apply integral_congr_ae
  filter_upwards [finiteSolutionRow_representative a ha N t hu] with r hr
  rw [hr]
  by_cases hp : r∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp,indicator_of_mem hp,halfSolution_apply]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,Complex.ofReal_zero,zero_mul]

/-- The actual finite transformed solution is entire in its genuine original complex energy.
Use: finite Green identities and their original spectral specializations use the same true finite transformed solution at arbitrary complex z.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: add the independently proved original reference energy analyticity and the entire original continuous-function reference solution composed with the genuine finite inverse-row coefficient functional. -/
theorem finiteTransformedSolution_analytic (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (z : ℂ) :
    AnalyticAt ℂ (finiteTransformedSolution a ha N t) z :=
  (solution_energy_analytic_half ha t.property z).add
    (((coefficientFunctional (finiteSolutionRow a ha N t:Space)).analyticAt _).comp (halfSolution_analytic a ha z))

/-- The genuine finite transformed solution takes the original real source value at every real energy.
Use: the actual finite real differential data use this same original finite GL transform, without any separately supplied reality condition.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original reference solution and actual source coefficient integral have their independently proved real-energy values. Complex inclusion preserves their sum. -/
theorem finiteTransformedSolution_real (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (E : ℝ) :
    finiteTransformedSolution a ha N t (E:ℂ)=
      (realSolution a E t+realCoefficient a (finiteSolutionRow a ha N t:Space) E:ℝ) := by
  change solution a (E:ℂ) t+coefficientFunctional (finiteSolutionRow a ha N t:Space) (halfSolution a ha (E:ℂ))=_
  rw [coefficient_halfSolution_real,← realSolution_cast,Complex.ofReal_add]

/-- The actual original finite diagonal converges uniformly to the original diagonal w on the full physical half interval.
Use: the original finite quasi-derivative relation passes to the actual transformed potential through the genuine diagonal limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: pull back the independently proved full physical-square uniform K^(N) limit along the genuine original diagonal. -/
theorem finiteKernelDiagonal_uniform_limit (a : ℝ) (ha : -1<a) :
    TendstoUniformly (finiteKernelDiagonal a ha) (kernelDiagonal a ha) atTop := by
  have h := (finiteTransformationKernel_uniform_limit a ha).comp (fun t : HalfInterval => (t,t))
  exact h

/-- The true original finite transformed-solution error is controlled by the genuine finite inverse-row error through the same original bounded source coefficient functional.
Use: finiteTransformedSolution_uniform_limit discharges the original actual u^(N) to u convergence at every complex energy.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original reference terms cancel, and linearity identifies the actual correction difference with the original coefficient functional of the true finite row difference. Its genuine bounded-linear norm gives the estimate. -/
theorem finiteTransformedSolution_error (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (z : ℂ) :
    ‖finiteTransformedSolution a ha N t z-transformedSolution a ha t z‖≤
      ‖coefficientInput (halfSolution a ha z)‖*‖finiteSolutionRow a ha N t-solutionRow a ha t‖ := by
  -- Only the actual inverse-row correction changes; the identical original reference values cancel exactly.
  rw [finiteTransformedSolution,transformedSolution_reference_form]
  have he : solution a z t+coefficientInput (halfSolution a ha z) (finiteSolutionRow a ha N t:Space)-
      (solution a z t+coefficientFunctional (solutionRow a ha t:Space) (halfSolution a ha z))=
      coefficientInput (halfSolution a ha z) ((finiteSolutionRow a ha N t:Space)-(solutionRow a ha t:Space)) := by
    rw [map_sub]
    change _=coefficientInput (halfSolution a ha z) (finiteSolutionRow a ha N t:Space)-
      coefficientInput (halfSolution a ha z) (solutionRow a ha t:Space)
    simp only [coefficientInput_apply]
    ring
  rw [he]
  exact (coefficientInput (halfSolution a ha z)).le_opNorm _

/-- The actual finite transformed solutions converge uniformly in the physical half-interval coordinate to the original u, at every original complex energy.
Use: the genuine finite quasi-derivative and Green identities can be passed to the original solution once their actual first-derivative convergence is proved.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual finite inverse rows have a proved uniform error bounded by one positive constant times the genuine original spectral tail. Apply the same original bounded source coefficient functional and the community metric uniform-limit criterion. -/
theorem finiteTransformedSolution_uniform_limit (a : ℝ) (ha : -1<a) (z : ℂ) :
    TendstoUniformly (fun N t => finiteTransformedSolution a ha N t z) (fun t => transformedSolution a ha t z) atTop := by
  -- The genuine original spectral error controls the original source coefficient functional uniformly in the physical endpoint.
  obtain ⟨D,_,hD⟩ := finiteSolutionRow_error a ha
  have he : Tendsto (fun N => (‖coefficientInput (halfSolution a ha z)‖*D)*finiteApproximationError a ha N) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (finiteApproximationError_limit a ha).const_mul (‖coefficientInput (halfSolution a ha z)‖*D)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hD,(tendsto_order.mp he).2 ε hε] with N hN hsmall t
  rw [dist_eq_norm,norm_sub_rev]
  exact ((finiteTransformedSolution_error a ha N t z).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hN t) (norm_nonneg (coefficientInput (halfSolution a ha z))))).trans_lt hsmall

end
end jacobi.GelfandLevitan
