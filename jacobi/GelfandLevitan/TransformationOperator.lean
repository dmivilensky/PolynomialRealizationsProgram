import jacobi.GelfandLevitan.FiniteKernelMaps
import jacobi.GelfandLevitan.SpatialSolution

/-!
Article: jacobi, Proposition C.2.
The Volterra operator acts on the original half-interval Hilbert space.
Its continuous representative is obtained from the already constructed
GL solution rows, so its kernel and its action on reference solutions
are consequences of the original integral equation.
Use: bounds the Volterra action uniformly in its output coordinate.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The continuous Hilbert-valued family of actual GL solution rows.
Use: bounds the Volterra action uniformly in its output coordinate.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def solutionRowMap (a : ℝ) (ha : -1<a) : C(HalfInterval,halfSubspace) :=
  ⟨solutionRow a ha,solutionRow_continuous a ha⟩

/-- The continuous representative of the Volterra integral of an arbitrary L2 input.
Use: transformationActionCLM and transformationOperator construct the actual operator in the GL factorization.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformationActionMap (a : ℝ) (ha : -1<a) (v : halfSubspace) : C(Interval,ℝ) where
  toFun t := inner ℝ (solutionRow a ha (halfClamp t)) v
  continuous_toFun := ((solutionRow_continuous a ha).comp halfClamp.continuous).inner continuous_const

/-- The genuine Volterra action as a bounded linear map to continuous representatives.
Use: its L2 embedding defines the original transformation operator without choosing values of L2 equivalence classes.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformationActionCLM (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] C(Interval,ℝ) :=
  LinearMap.mkContinuous
    { toFun := transformationActionMap a ha
      map_add' := by
        intro v w
        apply ContinuousMap.ext
        intro t
        change inner ℝ (solutionRow a ha (halfClamp t)) (v+w)=_
        exact inner_add_right _ _ _
      map_smul' := by
        intro r v
        apply ContinuousMap.ext
        intro t
        change inner ℝ (solutionRow a ha (halfClamp t)) (r • v)=
          r*inner ℝ (solutionRow a ha (halfClamp t)) v
        exact real_inner_smul_right (solutionRow a ha (halfClamp t)) v r }
    ‖solutionRowMap a ha‖ (fun v => by
      apply ((transformationActionMap a ha v).norm_le (by positivity)).mpr
      intro t
      exact (norm_inner_le_norm (𝕜 := ℝ) (solutionRow a ha (halfClamp t)) v).trans
        (mul_le_mul_of_nonneg_right ((solutionRowMap a ha).norm_coe_le_norm _) (norm_nonneg v)))

/-- The original bounded Volterra operator on the physical half interval.
Use: the factorization and the two transformed bases use precisely this operator.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformationOperator (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] halfSubspace :=
  rowEmbedding ∘L transformationActionCLM a ha

/-- The identity plus the actual Volterra operator.
Use: maps reference waves to transformed waves and enters the GL factorization.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformationPlus (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] halfSubspace :=
  ContinuousLinearMap.id ℝ halfSubspace+transformationOperator a ha

/-- The operator has exactly the actual continuous row-pairing representative on the original half interval.
Use: identifies the bounded Hilbert operator with the spatial Volterra integral in the factorization proof.
Article: jacobi, Proposition C.2.
Proof: apply the proved continuous-to-L2 half-projection representative to its actual output function. -/
theorem transformationOperator_ae (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    (transformationOperator a ha v:Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator (transformationActionMap a ha v) :=
  halfProjection_toLp_ae (transformationActionMap a ha v)

/-- The continuous Volterra action is the literal prefix integral against the original K.
Use: connects the actual bounded transformation operator to the printed GL transformation and its causal support.
Article: jacobi, Theorem 2.1.
Proof: substitute the proved prefix representative of the original solution row in the L2 inner product and use the measurable indicator integral identity. -/
theorem transformationActionMap_integral (a : ℝ) (ha : -1<a)
    (v : halfSubspace) (t : Interval) :
    transformationActionMap a ha v t=
      ∫ s:Interval in prefixSet (halfTime t),
        (v:Space) s*transformationKernel a ha (halfClamp t) (halfClamp s) := by
  -- The actual row is precisely the prefix indicator times K, so its L2 pairing is the genuine causal integral.
  change inner ℝ (solutionRow a ha (halfClamp t):Space) (v:Space)=_
  rw [L2.inner_def,← integral_indicator (prefixSet_measurable (halfTime t))]
  apply integral_congr_ae
  filter_upwards [solutionRow_representative a ha (halfClamp t)] with s hs
  rw [hs]
  change (v:Space) s*((prefixSet (halfTime t)).indicator
    (fun s => transformationKernel a ha (halfClamp t) (halfClamp s)) s)=_
  by_cases hp : s∈prefixSet (halfTime t)
  · rw [indicator_of_mem hp,indicator_of_mem hp]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,mul_zero]

/-- The actual transformed real solution as a continuous function on the common physical domain.
Use: its half-space embedding identifies transformationPlus applied to every original reference coefficient vector.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformedRealWave (a : ℝ) (ha : -1<a) (E : ℝ) : C(Interval,ℝ) :=
  ⟨fun t => (transformedSolution a ha (halfClamp t) (E:ℂ)).re,
    Complex.continuous_re.comp ((transformedSolution_continuous a ha (E:ℂ)).comp halfClamp.continuous)⟩

/-- The actual transformed reference wave as a vector of the original half-interval Hilbert space.
Use: its norming-weighted parity subsequences are the two systems in Two orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformedVector (a : ℝ) (ha : -1<a) (E : ℝ) : halfSubspace :=
  rowEmbedding (transformedRealWave a ha E)

/-- The original transformation sends every real reference wave to the actual constructed transformed wave.
Use: identifies the frame vectors in the GL factorization with u at the genuine target energies, rather than an abstract family.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: real-energy reality identifies u with f plus the original coefficient integral. The coefficient vector represents this same integral, so the continuous representatives agree before their common L2 embedding. -/
theorem transformationPlus_coefficientVector (a : ℝ) (ha : -1<a) (E : ℝ) :
    transformationPlus a ha (coefficientVector a ha E)=transformedVector a ha E := by
  -- Work with the genuine continuous representatives before applying the common quotient map.
  change rowEmbedding (realHalfWave a ha E)+
    rowEmbedding (transformationActionMap a ha (coefficientVector a ha E))=
      rowEmbedding (transformedRealWave a ha E)
  rw [← map_add]
  congr 1
  apply ContinuousMap.ext
  intro t
  change realSolution a E (halfTime t)+
    inner ℝ (solutionRow a ha (halfClamp t)) (coefficientVector a ha E)=
      (transformedSolution a ha (halfClamp t) (E:ℂ)).re
  rw [real_inner_comm,coefficientVector_inner,transformedSolution_real]
  rfl

end
end jacobi.GelfandLevitan
