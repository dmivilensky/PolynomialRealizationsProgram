import chebyshev1.Stochastic.IndependentMatrixRun

/-! Canonical sample and past sigma-algebras of an independent random-matrix sequence. -/
set_option backward.isDefEq.respectTransparency false
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω d : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

@[instance_reducible] def matrixSampleSigma (Z : ℕ → Ω → Matrix d d ℝ) (s : ℕ) : MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace (Matrix d d ℝ)).comap (Z s)

@[instance_reducible] def matrixPastSigma (Z : ℕ → Ω → Matrix d d ℝ) (s : ℕ) : MeasurableSpace Ω :=
  ⨆ t : ℕ, ⨆ (_ : t < s), matrixSampleSigma Z t

omit mΩ in
theorem matrixPastSigma_mono (Z : ℕ → Ω → Matrix d d ℝ) : Monotone (matrixPastSigma Z) := by
  intro s t hst
  apply iSup_le
  intro r
  apply iSup_le
  intro hrs
  exact le_iSup_of_le r (le_iSup_of_le (lt_of_lt_of_le hrs hst) le_rfl)

omit mΩ in
theorem matrixSampleSigma_le_future (Z : ℕ → Ω → Matrix d d ℝ) (s : ℕ) :
    matrixSampleSigma Z s ≤ matrixPastSigma Z (s+1) :=
  le_iSup_of_le s (le_iSup_of_le (Nat.lt_succ_self s) le_rfl)

theorem matrixPastSigma_le (Z : ℕ → Ω → Matrix d d ℝ) (hZ : ∀ s, Measurable (Z s)) (s : ℕ) :
    matrixPastSigma Z s ≤ mΩ := by
  apply iSup_le
  intro t
  apply iSup_le
  intro _
  exact (hZ t).comap_le

omit mΩ in
theorem matrixSampleSigma_entries (Z : ℕ → Ω → Matrix d d ℝ) (s : ℕ) (i j : d) :
    StronglyMeasurable[matrixSampleSigma Z s] (fun ω => Z s ω i j) := by
  let : MeasurableSpace Ω := matrixSampleSigma Z s
  have h : Measurable (Z s) := comap_measurable (Z s)
  exact h.eval_matrix.stronglyMeasurable

/-- Independence of the matrices implies independence of each sample from its entire past. -/
theorem matrixSampleSigma_indep_past (Z : ℕ → Ω → Matrix d d ℝ)
    (hZ : ∀ s, Measurable (Z s)) (hind : iIndepFun Z μ) (s : ℕ) :
    Indep (matrixSampleSigma Z s) (matrixPastSigma Z s) μ := by
  let : MeasurableSpace Ω := mΩ
  have hd : Disjoint ({s} : Set ℕ) (Set.Iio s) := by
    apply Set.disjoint_left.mpr
    intro r hr hrs
    have h := Set.mem_singleton_iff.mp hr
    subst r
    exact (lt_irrefl s) hrs
  have hh := indep_iSup_of_disjoint (fun t => (hZ t).comap_le) hind.iIndep hd
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iio,
    matrixSampleSigma, matrixPastSigma] using hh

end
end chebyshev1.Stochastic

namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology
variable {Ω d : Type*} [mΩ : MeasurableSpace Ω] [Fintype d] [DecidableEq d]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual random-matrix model follows directly from independent measurable L² samples. -/
def independentMatrixOracle_of_iIndepFun (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (hZ : ∀ s, Measurable (Z s)) (hind : iIndepFun Z μ)
    (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ)
    (hmean : ∀ s i j, (∫ ω, Z s ω i j ∂μ) = 0) :
    QuadraticObservationOracle (μ := μ) S H e0 (S.matrixCurvatureNoise H Z σ e0) N
      (independentMatrixObservations (μ := μ) Z) (σ^2) :=
  S.independentMatrixOracle H Z σ e0 (Stochastic.matrixPastSigma Z) (Stochastic.matrixSampleSigma Z)
    (Stochastic.matrixPastSigma_le Z hZ) (Stochastic.matrixPastSigma_mono Z)
    (Stochastic.matrixSampleSigma_le_future Z) (Stochastic.matrixSampleSigma_indep_past Z hZ hind)
    (Stochastic.matrixSampleSigma_entries Z) hZ2 hmean N

/-- The mean-square expansion of the actual run, stated directly for independent matrix samples. -/
theorem matrixCurvature_variance_of_iIndepFun (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (σ : ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (hZ : ∀ s, Measurable (Z s)) (hind : iIndepFun Z μ)
    (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ)
    (hmean : ∀ s i j, (∫ ω, Z s ω i j ∂μ) = 0) :
    (∫ ω, ‖S.matrixCurvatureError H Z σ e0 N ω -
      WithLp.toLp 2 (S.quadraticError H (WithLp.ofLp e0) N)‖^2 ∂μ) =
      σ^2 * S.matrixCurvatureGamma (μ := μ) H Z e0 N +
        S.matrixCurvatureRemainder (μ := μ) H Z σ e0 N := by
  have h := (S.independentMatrixOracle_of_iIndepFun H Z σ e0 N hZ hind hZ2 hmean).variance_expansion
  simpa only [QuadraticObservationOracle.variance, ← matrixCurvatureError_eq_stochasticError,
    matrixCurvatureGamma, matrixCurvatureRemainder] using h

theorem matrixCurvatureRemainder_isBigO_of_iIndepFun (S : TwoTerm) (H : Matrix d d ℝ)
    (Z : ℕ → Ω → Matrix d d ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (hZ : ∀ s, Measurable (Z s)) (hind : iIndepFun Z μ)
    (hZ2 : ∀ s i j, MemLp (fun ω => Z s ω i j) 2 μ)
    (hmean : ∀ s i j, (∫ ω, Z s ω i j ∂μ) = 0) :
    (fun σ => S.matrixCurvatureRemainder (μ := μ) H Z σ e0 N) =O[𝓝 0]
      (fun σ : ℝ => σ^4) := by
  exact S.observationNoiseRemainder_isBigO H e0 N (independentMatrixObservations (μ := μ) Z)
    (fun σ => S.matrixCurvatureNoise H Z σ e0)
    (fun σ => S.independentMatrixOracle_of_iIndepFun H Z σ e0 N hZ hind hZ2 hmean)

end
end chebyshev1.TwoTerm
