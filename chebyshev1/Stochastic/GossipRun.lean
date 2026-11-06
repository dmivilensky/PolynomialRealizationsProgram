import chebyshev1.Stochastic.GossipConditional
import chebyshev1.Stochastic.QuadraticCovarianceBounds

/-! The realized dropout-Laplacian recurrence satisfies the quadratic covariance
model. Adaptedness, square integrability, and covariance are derived. -/
namespace chebyshev1.TwoTerm
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
variable {Ω d e : Type*} [mΩ : MeasurableSpace Ω]
variable [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual two-term run, using the sampled, rescaled edge Laplacian at
every step. -/
def gossipError (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (n : ℕ) (ω : Ω) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (S.variableError (fun s => Stochastic.dropoutLaplacian p (A s) w b ω)
    (WithLp.ofLp e0) n)

/-- The actual oracle error evaluated at the current, realized state. -/
def gossipErrorNoise (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (s : ℕ) (ω : Ω) : EuclideanSpace ℝ d :=
  Stochastic.gossipOracleNoise p (A s) w b (WithLp.ofLp (S.gossipError p A w b e0 s ω)) ω

omit mΩ [DecidableEq d] [DecidableEq e] in
theorem gossipError_eq_stochasticError (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d) (n : ℕ) (ω : Ω) :
    S.gossipError p A w b e0 n ω = S.stochasticError (Stochastic.edgeLaplacian w b) e0
      (S.gossipErrorNoise p A w b e0) (fun _ _ => 0) n ω := by
  have he : ∀ n, S.perturbedError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0)
      (fun s => WithLp.ofLp (S.gossipErrorNoise p A w b e0 s ω)) (fun _ => 0) n =
      S.variableError (fun s => Stochastic.dropoutLaplacian p (A s) w b ω) (WithLp.ofLp e0) n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one =>
      simp [perturbedError, variableError, gossipErrorNoise, Stochastic.gossipOracleNoise,
        gossipError, Matrix.sub_mulVec]
    | more n ih0 ih1 =>
      rw [perturbedError, ih0, ih1]
      simp [variableError, gossipErrorNoise, Stochastic.gossipOracleNoise,
        gossipError, Matrix.sub_mulVec]
  exact congrArg (WithLp.toLp 2) (he n).symm

omit [DecidableEq e] in
/-- The realized states are adapted and square integrable under measurable
edge samples. Independence is unnecessary for this regularity statement. -/
theorem gossipError_regular (S : TwoTerm) (p : ℝ) (A : ℕ → e → Set Ω)
    (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hA : ∀ s i, MeasurableSet[m (s+1)] (A s i)) (n : ℕ) :
    StronglyMeasurable[m n] (S.gossipError p A w b e0 n) ∧
      MemLp (S.gossipError p A w b e0 n) 2 μ := by
  let : MeasurableSpace Ω := mΩ
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hnoise (s : ℕ) (hs : s < n) :
        StronglyMeasurable[m (s+1)] (S.gossipErrorNoise p A w b e0 s) ∧
          MemLp (S.gossipErrorNoise p A w b e0 s) 2 μ := by
      constructor
      · let : MeasurableSpace Ω := m (s+1)
        exact Stochastic.gossipOracleNoise_stronglyMeasurable p (A s) (hA s) w b _
          (((ih s hs).1).mono (hmono (by omega)))
      · exact Stochastic.gossipOracleNoise_memLp p (A s)
          (fun i => hm (s+1) _ (hA s i)) w b _ (ih s hs).2
    have hexp : S.gossipError p A w b e0 n = fun ω =>
        WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) n) +
          ∑ s ∈ Finset.range n, (-S.gamma s) •
            S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s
              (S.gossipErrorNoise p A w b e0 s ω) := by
      funext ω
      rw [S.gossipError_eq_stochasticError, S.stochasticError_expansion]
      simp only [map_zero, add_zero]
    rw [hexp]
    constructor
    · apply stronglyMeasurable_const.add
      apply Finset.stronglyMeasurable_fun_sum
      intro s hs
      have hs' : s+1 ≤ n := by have := Finset.mem_range.mp hs; omega
      exact (((S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s).continuous.comp_stronglyMeasurable
        ((hnoise s (Finset.mem_range.mp hs)).1.mono (hmono hs'))).const_smul (-S.gamma s))
    · have hterm (s : ℕ) (hs : s ∈ Finset.range n) : MemLp
          (fun ω => (-S.gamma s) • S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s
            (S.gossipErrorNoise p A w b e0 s ω)) 2 μ :=
        ((hnoise s (Finset.mem_range.mp hs)).2.continuousLinearMap_comp
          (S.forcingTailCLM (Stochastic.edgeLaplacian w b) n s)).const_smul (-S.gamma s)
      have hsum := memLp_finsetSum (Finset.range n) hterm
      have hc : MemLp (fun _ : Ω =>
          WithLp.toLp 2 (S.quadraticError (Stochastic.edgeLaplacian w b) (WithLp.ofLp e0) n)) 2 μ :=
        memLp_const _
      exact hc.add hsum

/-- Deterministic edge covariance maps for the full nominal Laplacian. -/
def gossipCovarianceResponse (w : e → ℝ) (b : e → d → ℝ) :
    ℕ → e → EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d :=
  fun _ i => Stochastic.gossipEdgeResponse (w i) (b i) (ContinuousLinearMap.id ℝ _)

/-- The actual dropout recurrence, with all fields of its covariance model
proved from fresh edge samples. -/
def gossipQuadraticOracle (S : TwoTerm) (p : ℝ) (hp : p < 1)
    (A : ℕ → e → Set Ω) (w : e → ℝ) (b : e → d → ℝ) (e0 : EuclideanSpace ℝ d)
    (m q : ℕ → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ) (hmono : Monotone m)
    (hfuture : ∀ s, q s ≤ m (s+1)) (hfresh : ∀ s, Indep (q s) (m s) μ)
    (hA : ∀ s i, MeasurableSet[q s] (A s i)) (hind : ∀ s, iIndepSet (A s) μ)
    (hprob : ∀ s i, μ.real (A s i) = 1-p) (N : ℕ) :
    QuadraticOracle (μ := μ) S (Stochastic.edgeLaplacian w b) e0
      (S.gossipErrorNoise p A w b e0) N (gossipCovarianceResponse w b) (p/(1-p)) := by
  let : MeasurableSpace Ω := mΩ
  have hAfull (s : ℕ) (i : e) : MeasurableSet[m (s+1)] (A s i) := hfuture s _ (hA s i)
  have hstate (s : ℕ) := S.gossipError_regular (μ := μ) p A w b e0 m hm hmono hAfull s
  refine {
    filtration := m
    le := hm
    mono := hmono
    adapted := ?_
    squareIntegrable := ?_
    centered := ?_
    covariance := ?_ }
  · intro s _
    let : MeasurableSpace Ω := m (s+1)
    exact Stochastic.gossipOracleNoise_stronglyMeasurable p (A s) (hAfull s) w b _
      ((hstate s).1.mono (hmono (Nat.le_succ s)))
  · intro s _
    exact Stochastic.gossipOracleNoise_memLp p (A s) (fun i => hm (s+1) _ (hAfull s i))
      w b _ (hstate s).2
  · intro s _
    change μ[fun ω => Stochastic.gossipOracleNoise p (A s) w b
      (WithLp.ofLp (S.gossipError p A w b e0 s ω)) ω | m s] =ᵐ[μ] 0
    have hh := Stochastic.gossipOracleNoise_conditional_moments p hp (m s) (q s)
      (hm s) ((hfuture s).trans (hm (s+1))) (hfresh s) (A s) (hA s) (hind s) (hprob s)
      w b (S.gossipError p A w b e0 s) (hstate s).1 (hstate s).2 (ContinuousLinearMap.id ℝ _)
    simpa only [ContinuousLinearMap.id_apply] using hh.1
  · intro s _ T
    have hh := (Stochastic.gossipOracleNoise_conditional_moments p hp (m s) (q s)
      (hm s) ((hfuture s).trans (hm (s+1))) (hfresh s) (A s) (hA s) (hind s) (hprob s)
      w b (S.gossipError p A w b e0 s) (hstate s).1 (hstate s).2 T).2
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
    simp only [gossipCovarianceResponse, Stochastic.gossipEdgeResponse_apply,
      ContinuousLinearMap.id_apply, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

end
end chebyshev1.TwoTerm
