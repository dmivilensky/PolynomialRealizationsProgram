import chebyshev1.Stochastic.GossipRun

/-! The actual dropout run has leading variance `p * Gamma`, with a
nonnegative, uniformly quadratic remainder as the dropout probability vanishes. -/
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators Topology
variable {Ω d e : Type*} [mΩ : MeasurableSpace Ω]
variable [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Leading graph covariance, evaluated along the deterministic nominal run. -/
def gossipGamma (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (e0 : EuclideanSpace ℝ d) (N : ℕ) : ℝ :=
  ∑ s ∈ Finset.range N, (S.gamma s)^2 * ∑ i,
    (w i)^2 * (dotProduct (b i)
      (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) s))^2 *
        ‖S.forcingTailCLM (Stochastic.edgeLaplacian w b) N s (WithLp.toLp 2 (b i))‖^2

omit mΩ [DecidableEq e] in
theorem gossipGamma_nonneg (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (e0 : EuclideanSpace ℝ d) (N : ℕ) : 0 ≤ S.gossipGamma w b e0 N := by
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

omit mΩ [DecidableEq e] in
theorem gossipGamma_eq_quadraticNoiseGamma (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (e0 : EuclideanSpace ℝ d) (N : ℕ) :
    S.gossipGamma w b e0 N = S.quadraticNoiseGamma (Stochastic.edgeLaplacian w b) e0 N
      (gossipCovarianceResponse w b) := by
  unfold gossipGamma quadraticNoiseGamma
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [gossipCovarianceResponse, Stochastic.gossipEdgeResponse_apply,
    ContinuousLinearMap.id_apply, map_smul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]

omit mΩ [DecidableEq e] in
theorem gossipGamma_residual (S : TwoTerm) (w : e → ℝ) (b : e → d → ℝ)
    (e0 : EuclideanSpace ℝ d) (N : ℕ) :
    S.gossipGamma w b e0 N = ∑ s ∈ Finset.range N, (S.gamma s)^2 * ∑ i,
      (w i)^2 * (dotProduct (b i)
        ((Polynomial.aeval (Stochastic.edgeLaplacian w b)
          (S.realization.residualPolynomial s)).mulVec (WithLp.ofLp e0)))^2 *
          ‖S.forcingTailCLM (Stochastic.edgeLaplacian w b) N s (WithLp.toLp 2 (b i))‖^2 := by
  unfold gossipGamma
  simp_rw [S.quadraticError_eq_transfer, Realization.operatorTransfer_eq_aeval]

/-- The total correction when the leading coefficient is expressed using `p`
rather than `p/(1-p)`. -/
def gossipRemainder (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ) : ℝ :=
  (p/(1-p)-p)*S.gossipGamma w b e0 N +
    S.quadraticNoiseRemainder (μ := μ) (Stochastic.edgeLaplacian w b) e0 N
      (S.gossipErrorNoise p A w b e0) (gossipCovarianceResponse w b) (p/(1-p))

omit [DecidableEq e] [IsProbabilityMeasure μ] in
theorem gossipRemainder_nonneg (S : TwoTerm) (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ) :
    0 ≤ S.gossipRemainder (μ := μ) p A w b e0 N := by
  have hq : 0 ≤ p/(1-p) := div_nonneg hp0 (sub_pos.mpr hp).le
  have hqp : 0 ≤ p/(1-p)-p := by
    rw [show p/(1-p)-p = p^2/(1-p) by field_simp [(sub_pos.mpr hp).ne']; ring]
    exact div_nonneg (sq_nonneg _) (sub_pos.mpr hp).le
  exact add_nonneg (mul_nonneg hqp (S.gossipGamma_nonneg w b e0 N))
    (S.quadraticNoiseRemainder_nonneg _ _ _ _ _ _ hq)

omit [DecidableEq e] in
/-- Uniform quadratic bound for the actual corrected remainder. -/
theorem gossipRemainder_bound (S : TwoTerm) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (R : QuadraticOracle (μ := μ) S (Stochastic.edgeLaplacian w b) e0
      (S.gossipErrorNoise p A w b e0) N (gossipCovarianceResponse w b) (p/(1-p))) :
    S.gossipRemainder (μ := μ) p A w b e0 N ≤ p^2 *
      (2*S.gossipGamma w b e0 N +
        4*S.covarianceRemainderBound (Stochastic.edgeLaplacian w b) e0 N (gossipCovarianceResponse w b)) := by
  have hd : 0 < 1-p := by linarith
  have hq : 0 ≤ p/(1-p) := div_nonneg hp0 hd.le
  have hq1 : p/(1-p) ≤ 1 := by rw [div_le_iff₀ hd]; linarith
  have hq2 : p/(1-p) ≤ 2*p := by rw [div_le_iff₀ hd]; nlinarith
  have hqsq : (p/(1-p))^2 ≤ 4*p^2 := by nlinarith
  have hqp : p/(1-p)-p ≤ 2*p^2 := by
    rw [show p/(1-p)-p = p^2/(1-p) by field_simp [hd.ne']; ring]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sq_nonneg p) (by linarith : 0 ≤ 1-2*p)]
  have hlead := mul_le_mul_of_nonneg_right hqp (S.gossipGamma_nonneg w b e0 N)
  have hrem := (R.remainder_bound hq hq1).trans
    (mul_le_mul_of_nonneg_right hqsq (S.covarianceRemainderBound_nonneg
      (Stochastic.edgeLaplacian w b) e0 N (gossipCovarianceResponse w b)))
  unfold gossipRemainder
  nlinarith

/-- Exact leading-plus-remainder variance for the realized dropout run. -/
theorem gossipError_variance_expansion (S : TwoTerm) (p : ℝ) (hp : p < 1)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (m q : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hfuture : ∀ s, q s ≤ m (s+1)) (hfresh : ∀ s, Indep (q s) (m s) μ)
    (hA : ∀ s i, MeasurableSet[q s] (A s i)) (hind : ∀ s, iIndepSet (A s) μ)
    (hprob : ∀ s i, μ.real (A s i) = 1-p) (N : ℕ) :
    (∫ ω, ‖S.gossipError p A w b e0 N ω-
      WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 ∂μ) =
      p*S.gossipGamma w b e0 N + S.gossipRemainder (μ := μ) p A w b e0 N := by
  let R := S.gossipQuadraticOracle p hp A w b e0 m q hm hmono hfuture hfresh hA hind hprob N
  have hh := S.stochasticError_quadratic_covariance (Stochastic.edgeLaplacian w b) e0
    (S.gossipErrorNoise p A w b e0) N R.filtration R.le R.mono R.adapted R.squareIntegrable
      R.centered (gossipCovarianceResponse w b) (p/(1-p)) R.covariance
  simp_rw [← S.gossipError_eq_stochasticError] at hh
  rw [← S.gossipGamma_eq_quadraticNoiseGamma w b e0 N] at hh
  rw [hh]
  unfold gossipRemainder
  ring

/-- Terminal mean-square error for the actual run, with the deterministic
residual and the explicit graph covariance coefficient. -/
theorem gossipError_secondMoment_expansion (S : TwoTerm) (p : ℝ) (hp : p < 1)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (m q : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hfuture : ∀ s, q s ≤ m (s+1)) (hfresh : ∀ s, Indep (q s) (m s) μ)
    (hA : ∀ s i, MeasurableSet[q s] (A s i)) (hind : ∀ s, iIndepSet (A s) μ)
    (hprob : ∀ s i, μ.real (A s i) = 1-p) (N : ℕ) :
    (∫ ω, ‖S.gossipError p A w b e0 N ω‖^2 ∂μ) =
      ‖WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 +
        p*S.gossipGamma w b e0 N + S.gossipRemainder (μ := μ) p A w b e0 N := by
  let R := S.gossipQuadraticOracle p hp A w b e0 m q hm hmono hfuture hfresh hA hind hprob N
  have hh := R.secondMoment_decomposition (t := N) le_rfl
  change (∫ ω, ‖S.stochasticError (Stochastic.edgeLaplacian w b) e0
      (S.gossipErrorNoise p A w b e0) (fun _ _ => 0) N ω‖^2 ∂μ) =
      ‖WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 +
        (∫ ω, ‖S.stochasticError (Stochastic.edgeLaplacian w b) e0
          (S.gossipErrorNoise p A w b e0) (fun _ _ => 0) N ω-
            WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) N)‖^2 ∂μ) at hh
  simp_rw [← S.gossipError_eq_stochasticError] at hh
  rw [S.gossipError_variance_expansion p hp A w b e0 m q hm hmono hfuture hfresh hA hind hprob N] at hh
  exact hh.trans (by ring)

/-- The actual family of dropout runs has a nonnegative `O(p²)` correction
relative to the leading `p * Gamma`, under fresh-edge hypotheses at each `p`. -/
theorem gossipRemainder_isBigO (S : TwoTerm) (A : ℝ → ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (N : ℕ)
    (m q : ℝ → ℕ → MeasurableSpace Ω)
    (hm : ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ s, m p s ≤ mΩ)
    (hmono : ∀ p ∈ Set.Icc (0:ℝ) (1/2), Monotone (m p))
    (hfuture : ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ s, q p s ≤ m p (s+1))
    (hfresh : ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ s, Indep (q p s) (m p s) μ)
    (hA : ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ s i, MeasurableSet[q p s] (A p s i))
    (hind : ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ s, iIndepSet (A p s) μ)
    (hprob : ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ s i, μ.real (A p s i) = 1-p) :
    (fun p => S.gossipRemainder (μ := μ) p (A p) w b e0 N)
      =O[𝓝[Set.Ici 0] 0] (fun p : ℝ => p^2) := by
  apply IsBigO.of_bound (2*S.gossipGamma w b e0 N +
    4*S.covarianceRemainderBound (Stochastic.edgeLaplacian w b) e0 N (gossipCovarianceResponse w b))
  have hsmall : ∀ᶠ p : ℝ in 𝓝[Set.Ici 0] 0, p ≤ 1/2 :=
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with p hp0 hp1
  have hp0' : 0 ≤ p := hp0
  have hp : p < 1 := by linarith
  have hmem : p ∈ Set.Icc (0:ℝ) (1/2) := ⟨hp0',hp1⟩
  let R := S.gossipQuadraticOracle p hp (A p) w b e0 (m p) (q p) (hm p hmem)
    (hmono p hmem) (hfuture p hmem) (hfresh p hmem) (hA p hmem) (hind p hmem) (hprob p hmem) N
  have hb := S.gossipRemainder_bound p hp0' hp1 (A p) w b e0 N R
  have hn := S.gossipRemainder_nonneg (μ := μ) p hp0' hp (A p) w b e0 N
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p)]
  exact hb.trans_eq (by ring)

end
end chebyshev1.TwoTerm
