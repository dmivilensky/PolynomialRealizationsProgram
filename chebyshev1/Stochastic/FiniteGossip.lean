import chebyshev1.Stochastic.GossipAsymptotics

/-! The actual dropout run through a fixed finite horizon needs edge assumptions
only at the sampled steps.  No infinite independent extension of the probability
space is required.  The covariance remainder retains the exact p/(1-p) prefactor. -/
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators Topology
variable {Ω d e : Type*} [mΩ : MeasurableSpace Ω]
variable [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
set_option maxHeartbeats 800000

omit [DecidableEq e] in
/-- Adaptedness and L² regularity use only edge measurability before N. -/
theorem gossipError_regular_finite (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (N : ℕ) (hA : ∀ s < N, ∀ i, MeasurableSet[m (s+1)] (A s i)) :
    ∀ n ≤ N, StronglyMeasurable[m n] (S.gossipError p A w b e0 n) ∧
      MemLp (S.gossipError p A w b e0 n) 2 μ := by
  let : MeasurableSpace Ω := mΩ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hnoise (s : ℕ) (hs : s < n) :
        StronglyMeasurable[m (s+1)] (S.gossipErrorNoise p A w b e0 s) ∧
          MemLp (S.gossipErrorNoise p A w b e0 s) 2 μ := by
      have hsN : s < N := lt_of_lt_of_le hs hn
      have hstate := ih s hs (by omega)
      constructor
      · let : MeasurableSpace Ω := m (s+1)
        exact Stochastic.gossipOracleNoise_stronglyMeasurable p (A s) (hA s hsN) w b _
          (hstate.1.mono (hmono (Nat.le_succ s)))
      · exact Stochastic.gossipOracleNoise_memLp p (A s)
          (fun i => hm (s+1) _ (hA s hsN i)) w b _ hstate.2
    have hexp : S.gossipError p A w b e0 n = fun ω =>
        WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) n) +
          ∑ s ∈ Finset.range n, (-S.gamma s) •
            S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s
              (S.gossipErrorNoise p A w b e0 s ω) := by
      funext ω
      rw [S.gossipError_eq_stochasticError,S.stochasticError_expansion]
      simp only [map_zero,add_zero]
    rw [hexp]
    constructor
    · apply stronglyMeasurable_const.add
      apply Finset.stronglyMeasurable_fun_sum
      intro s hs
      have hs' : s+1 ≤ n := by have := Finset.mem_range.mp hs; omega
      exact ((S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s).continuous.comp_stronglyMeasurable
        ((hnoise s (Finset.mem_range.mp hs)).1.mono (hmono hs'))).const_smul (-S.gamma s)
    · have hterm (s : ℕ) (hs : s ∈ Finset.range n) : MemLp
          (fun ω => (-S.gamma s) • S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s
            (S.gossipErrorNoise p A w b e0 s ω)) 2 μ :=
        ((hnoise s (Finset.mem_range.mp hs)).2.continuousLinearMap_comp
          (S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s)).const_smul (-S.gamma s)
      have hc : MemLp (fun _ : Ω =>
          WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) n)) 2 μ :=
        memLp_const _
      exact hc.add (memLp_finsetSum (Finset.range n) hterm)

/-- A covariance-model constructor for the actual run, with all random edge
hypotheses restricted to s<N. -/
def gossipQuadraticOracle_finite (S : TwoTerm) (p : ℝ) (hp : p < 1)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (N : ℕ) (m q : ℕ → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hfuture : ∀ s < N, q s ≤ m (s+1))
    (hfresh : ∀ s < N, Indep (q s) (m s) μ)
    (hA : ∀ s < N, ∀ i, MeasurableSet[q s] (A s i))
    (hind : ∀ s < N, iIndepSet (A s) μ)
    (hprob : ∀ s < N, ∀ i, μ.real (A s i)=1-p) :
    QuadraticOracle (μ := μ) S (Stochastic.edgeLaplacian w b) e0
      (S.gossipErrorNoise p A w b e0) N (gossipCovarianceResponse w b) (p/(1-p)) := by
  let : MeasurableSpace Ω := mΩ
  have hAfull (s : ℕ) (hs : s < N) (i : e) : MeasurableSet[m (s+1)] (A s i) :=
    hfuture s hs _ (hA s hs i)
  have hstate := S.gossipError_regular_finite (μ := μ) p A w b e0 m hm hmono N hAfull
  refine {
    filtration := m
    le := hm
    mono := hmono
    adapted := ?_
    squareIntegrable := ?_
    centered := ?_
    covariance := ?_ }
  · intro s hs
    let : MeasurableSpace Ω := m (s+1)
    exact Stochastic.gossipOracleNoise_stronglyMeasurable p (A s) (hAfull s hs) w b _
      ((hstate s (by omega)).1.mono (hmono (Nat.le_succ s)))
  · intro s hs
    exact Stochastic.gossipOracleNoise_memLp p (A s) (fun i => hm (s+1) _ (hAfull s hs i))
      w b _ (hstate s (by omega)).2
  · intro s hs
    change μ[fun ω => Stochastic.gossipOracleNoise p (A s) w b
      (WithLp.ofLp (S.gossipError p A w b e0 s ω)) ω | m s] =ᵐ[μ] 0
    have hh := Stochastic.gossipOracleNoise_conditional_moments p hp (m s) (q s)
      (hm s) ((hfuture s hs).trans (hm (s+1))) (hfresh s hs) (A s) (hA s hs)
      (hind s hs) (hprob s hs) w b (S.gossipError p A w b e0 s)
      (hstate s (by omega)).1 (hstate s (by omega)).2 (ContinuousLinearMap.id ℝ _)
    simpa only [ContinuousLinearMap.id_apply] using hh.1
  · intro s hs T
    have hh := (Stochastic.gossipOracleNoise_conditional_moments p hp (m s) (q s)
      (hm s) ((hfuture s hs).trans (hm (s+1))) (hfresh s hs) (A s) (hA s hs)
      (hind s hs) (hprob s hs) w b (S.gossipError p A w b e0 s)
      (hstate s (by omega)).1 (hstate s (by omega)).2 T).2
    refine hh.trans (Eventually.of_forall (fun ω => ?_))
    change p/(1-p)*(∑ i, (w i)^2*(dotProduct (b i)
      (WithLp.ofLp (S.gossipError p A w b e0 s ω)))^2*‖T (WithLp.toLp 2 (b i))‖^2) =
        p/(1-p)*∑ i, ‖T (gossipCovarianceResponse w b s i
          (S.stochasticError (Stochastic.edgeLaplacian w b) e0
            (S.gossipErrorNoise p A w b e0) (fun _ _ => 0) s ω))‖^2
    rw [← S.gossipError_eq_stochasticError]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [gossipCovarianceResponse,Stochastic.gossipEdgeResponse_apply,
      ContinuousLinearMap.id_apply,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

/-- The exact-prefactor covariance remainder of the actual finite dropout run. -/
def gossipCovarianceRemainder (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ) : ℝ :=
  S.quadraticNoiseRemainder (μ := μ) (Stochastic.edgeLaplacian w b) e0 N
    (S.gossipErrorNoise p A w b e0) (gossipCovarianceResponse w b) (p/(1-p))

omit [DecidableEq e] [IsProbabilityMeasure μ] in
theorem gossipCovarianceRemainder_nonneg (S : TwoTerm) (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ) :
    0 ≤ S.gossipCovarianceRemainder (μ := μ) p A w b e0 N :=
  S.quadraticNoiseRemainder_nonneg _ _ _ _ _ _
    (div_nonneg hp0 (sub_pos.mpr hp).le)

section FiniteData
variable (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
variable (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
variable (m q : ℕ → MeasurableSpace Ω)
variable (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
variable (hfuture : ∀ s < N, q s ≤ m (s+1))
variable (hfresh : ∀ s < N, Indep (q s) (m s) μ)
variable (hA : ∀ s < N, ∀ i, MeasurableSet[q s] (A s i))
variable (hind : ∀ s < N, iIndepSet (A s) μ)
variable (hprob : ∀ s < N, ∀ i, μ.real (A s i)=1-p)
include hm hmono hfuture hfresh hA hind hprob

/-- The actual finite run has the nominal mean. -/
theorem gossipError_mean_finite (hp : p < 1) :
    (∫ ω, S.gossipError p A w b e0 N ω ∂μ) =
      WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N) := by
  let R := S.gossipQuadraticOracle_finite p hp A w b e0 N m q hm hmono hfuture hfresh hA hind hprob
  have hh := R.mean (t := N) le_rfl
  simpa only [← S.gossipError_eq_stochasticError] using hh

/-- Exact variance with leading p/(1-p) times the graph Gamma and nonnegative remainder. -/
theorem gossipError_variance_finite (hp : p < 1) :
    (∫ ω, ‖S.gossipError p A w b e0 N ω-
      WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 ∂μ) =
      (p/(1-p))*S.gossipGamma w b e0 N + S.gossipCovarianceRemainder (μ := μ) p A w b e0 N := by
  let R := S.gossipQuadraticOracle_finite p hp A w b e0 N m q hm hmono hfuture hfresh hA hind hprob
  have hh := S.stochasticError_quadratic_covariance (Stochastic.edgeLaplacian w b) e0
    (S.gossipErrorNoise p A w b e0) N R.filtration R.le R.mono R.adapted R.squareIntegrable
      R.centered (gossipCovarianceResponse w b) (p/(1-p)) R.covariance
  simp_rw [← S.gossipError_eq_stochasticError] at hh
  simpa only [← S.gossipGamma_eq_quadraticNoiseGamma w b e0 N,gossipCovarianceRemainder] using hh

/-- Exact terminal second moment of the same finite run. -/
theorem gossipError_secondMoment_finite (hp : p < 1) :
    (∫ ω, ‖S.gossipError p A w b e0 N ω‖^2 ∂μ) =
      ‖WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 +
        (p/(1-p))*S.gossipGamma w b e0 N + S.gossipCovarianceRemainder (μ := μ) p A w b e0 N := by
  let R := S.gossipQuadraticOracle_finite p hp A w b e0 N m q hm hmono hfuture hfresh hA hind hprob
  have hh := R.secondMoment_decomposition (t := N) le_rfl
  change (∫ ω, ‖S.stochasticError (Stochastic.edgeLaplacian w b) e0
    (S.gossipErrorNoise p A w b e0) (fun _ _ => 0) N ω‖^2 ∂μ) =
      ‖WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 +
      (∫ ω, ‖S.stochasticError (Stochastic.edgeLaplacian w b) e0
        (S.gossipErrorNoise p A w b e0) (fun _ _ => 0) N ω-
          WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 ∂μ) at hh
  simp_rw [← S.gossipError_eq_stochasticError] at hh
  rw [S.gossipError_variance_finite p A w b e0 N m q hm hmono hfuture hfresh hA hind hprob hp] at hh
  exact hh.trans (by ring)

/-- A finite-horizon bound whose constant depends only on the fixed nominal data. -/
theorem gossipCovarianceRemainder_bound_finite (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    S.gossipCovarianceRemainder (μ := μ) p A w b e0 N ≤
      4*p^2*S.covarianceRemainderBound (Stochastic.edgeLaplacian w b) e0 N
        (gossipCovarianceResponse w b) := by
  have hp : p < 1 := by linarith
  have hd : 0 < 1-p := by linarith
  let R := S.gossipQuadraticOracle_finite p hp A w b e0 N m q hm hmono hfuture hfresh hA hind hprob
  have hq : 0 ≤ p/(1-p) := div_nonneg hp0 hd.le
  have hq1 : p/(1-p) ≤ 1 := by rw [div_le_iff₀ hd]; linarith
  have hq2 : p/(1-p) ≤ 2*p := by rw [div_le_iff₀ hd]; nlinarith
  have hsq : (p/(1-p))^2 ≤ 4*p^2 := by nlinarith
  exact (R.remainder_bound hq hq1).trans (mul_le_mul_of_nonneg_right hsq
    (S.covarianceRemainderBound_nonneg (Stochastic.edgeLaplacian w b) e0 N (gossipCovarianceResponse w b)))

end FiniteData

/-- The primitive edge-sampling hypotheses on a fixed finite horizon.  The law
is an explicit parameter, so a Bernoulli family may vary its law with p. -/
structure FiniteGossipSamples (ν : Measure Ω) (p : ℝ) (A : ℕ → e → Set Ω) (N : ℕ) where
  probability : IsProbabilityMeasure ν
  filtration : ℕ → MeasurableSpace Ω
  sampleSigma : ℕ → MeasurableSpace Ω
  le : ∀ s, filtration s ≤ mΩ
  mono : Monotone filtration
  future : ∀ s < N, sampleSigma s ≤ filtration (s+1)
  fresh : ∀ s < N, Indep (sampleSigma s) (filtration s) ν
  measurable : ∀ s < N, ∀ i, MeasurableSet[sampleSigma s] (A s i)
  independent : ∀ s < N, iIndepSet (A s) ν
  activation : ∀ s < N, ∀ i, ν.real (A s i)=1-p

/-- The actual finite-family remainder is O(p²), even when its probability law
varies with p.  Finite edge hypotheses need hold only near zero; the explicit
uniform constant contains no probability measure or edge realization. -/
theorem gossipCovarianceRemainder_isBigO_varyingMeasure_finite (S : TwoTerm)
    (ν : ℝ → Measure Ω) (A : ℝ → ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (models : ∀ᶠ p : ℝ in 𝓝[Set.Ici 0] 0, Nonempty (FiniteGossipSamples (ν p) p (A p) N)) :
    (fun p => S.gossipCovarianceRemainder (μ := ν p) p (A p) w b e0 N)
      =O[𝓝[Set.Ici 0] 0] (fun p : ℝ => p^2) := by
  apply IsBigO.of_bound
    (4*S.covarianceRemainderBound (Stochastic.edgeLaplacian w b) e0 N (gossipCovarianceResponse w b))
  have hsmall : ∀ᶠ p : ℝ in 𝓝[Set.Ici 0] 0, p ≤ 1/2 :=
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [models,self_mem_nhdsWithin,hsmall] with p hmodel hp0 hp1
  obtain ⟨D⟩ := hmodel
  let : IsProbabilityMeasure (ν p) := D.probability
  have hp0' : 0 ≤ p := hp0
  have hp : p < 1 := by linarith
  have hb := S.gossipCovarianceRemainder_bound_finite (μ := ν p) p (A p) w b e0 N
    D.filtration D.sampleSigma D.le D.mono D.future D.fresh D.measurable D.independent D.activation hp0' hp1
  have hn := S.gossipCovarianceRemainder_nonneg (μ := ν p) p hp0' hp (A p) w b e0 N
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg p)]
  exact hb.trans_eq (by ring)

end
end chebyshev1.TwoTerm
