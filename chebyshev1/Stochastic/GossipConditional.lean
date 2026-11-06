import chebyshev1.Stochastic.GossipGraph
import chebyshev1.Stochastic.PairedNoise
import Mathlib.Probability.ConditionalExpectation

/-! Fresh independent edge dropout has exact conditional covariance even when
the current state is random and measurable with respect to the past. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators RealInnerProductSpace ENNReal

variable {Ω e E : Type*} [mΩ : MeasurableSpace Ω]
variable [Fintype e] [DecidableEq e]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem dropoutNoise_measurable (p : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    Measurable (dropoutNoise p A) := by
  change Measurable (fun ω => A.indicator (fun _ : Ω => (1:ℝ)) ω/(1-p)-1)
  exact ((measurable_const.indicator hA).div_const _).sub_const _

theorem dropoutNoise_memLp_top (p : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    MemLp (dropoutNoise p A) ∞ μ := by
  apply MemLp.of_bound
    (dropoutNoise_measurable p hA).aestronglyMeasurable
    (|(1-p)⁻¹|+1)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs]
  by_cases hω : ω ∈ A
  · simp only [dropoutNoise, Set.indicator_of_mem hω, Pi.one_apply, one_div]
    simpa only [sub_eq_add_neg, abs_neg, abs_one] using abs_add_le ((1-p)⁻¹) (-1:ℝ)
  · simp only [dropoutNoise, Set.indicator_of_notMem hω, zero_div, zero_sub, abs_neg, abs_one]
    linarith [abs_nonneg ((1-p)⁻¹)]

/-- Conditional first and second moments for random past-measurable edge
responses. Integrability follows from their L² hypotheses and bounded dropout. -/
theorem dropout_sum_conditional_moments (p : ℝ) (hp : p < 1)
    (m q : MeasurableSpace Ω) (hm : m ≤ mΩ) (hq : q ≤ mΩ)
    (hfresh : Indep q m μ) (A : e → Set Ω)
    (hA : ∀ i, MeasurableSet[q] (A i)) (hind : iIndepSet A μ)
    (hprob : ∀ i, μ.real (A i) = 1-p) (V : e → Ω → E)
    (hV : ∀ i, StronglyMeasurable[m] (V i)) (hV2 : ∀ i, MemLp (V i) 2 μ) :
    μ[fun ω => ∑ i, dropoutNoise p (A i) ω • V i ω | m] =ᵐ[μ] 0 ∧
    μ[fun ω => ‖∑ i, dropoutNoise p (A i) ω • V i ω‖^2 | m] =ᵐ[μ]
      (fun ω => p/(1-p)*∑ i, ‖V i ω‖^2) := by
  let : MeasurableSpace Ω := mΩ
  let z := fun i => dropoutNoise p (A i)
  let Y := fun i ω => z i ω • V i ω
  have hzq (i : e) : StronglyMeasurable[q] (z i) := by
    let : MeasurableSpace Ω := q
    exact (dropoutNoise_measurable p (hA i)).stronglyMeasurable
  have hzm (i : e) : Measurable (z i) := (hzq i).measurable.mono hq le_rfl
  have hzint (i : e) : Integrable (z i) μ := dropoutNoise_integrable p (hq _ (hA i))
  have hz2int (i : e) : Integrable (fun ω => z i ω^2) μ :=
    dropoutNoise_sq_integrable p (hq _ (hA i))
  have hzmean (i : e) : (∫ ω, z i ω ∂μ) = 0 :=
    dropoutNoise_mean p (hq _ (hA i)) (hprob i) hp
  have hzcond (i : e) : μ[z i | m] =ᵐ[μ] 0 := by
    have hh := condExp_indep_eq hq hm (hzq i) hfresh
    simpa only [hzmean, Pi.zero_def] using hh
  have hY2 (i : e) : MemLp (Y i) 2 μ :=
    (dropoutNoise_memLp_top p (hq _ (hA i))).smul (hV2 i)
  have hYint (i : e) : Integrable (Y i) μ := (hY2 i).integrable (by norm_num)
  have hYcond (i : e) : μ[Y i | m] =ᵐ[μ] 0 := by
    have hh := condExp_smul_of_aestronglyMeasurable_right (hzint i) (hYint i)
      (hV i).aestronglyMeasurable
    have hfun : z i • V i = Y i := by funext ω; rfl
    rw [hfun] at hh
    filter_upwards [hh, hzcond i] with ω hh hz
    change μ[Y i | m] ω = μ[z i | m] ω • V i ω at hh
    simpa only [hz, Pi.zero_apply, zero_smul] using hh
  constructor
  · have hh := condExp_finsetSum (s := Finset.univ) (fun i _ => hYint i) m
    filter_upwards [hh, ae_all_iff.mpr hYcond] with ω hh hall
    have hfun : (fun ω => ∑ i, Y i ω) = ∑ i, Y i := by funext ω; simp
    change μ[fun ω => ∑ i, Y i ω | m] ω = 0
    rw [hfun]
    rw [hh]
    simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i _ => hall i)
  · have hzi (i j : e) : Integrable (fun ω => z i ω*z j ω) μ := by
      by_cases hij : i = j
      · subst j
        simpa only [sq] using hz2int i
      · exact ((dropoutNoise_independent hind p).indepFun hij).integrable_mul (hzint i) (hzint j)
    have hpaircond (i j : e) : μ[fun ω => z i ω*z j ω | m] =ᵐ[μ]
        (fun _ => if i = j then p/(1-p) else 0) := by
      have hh := condExp_indep_eq hq hm ((hzq i).mul (hzq j)) hfresh
      have hfun : z i*z j = fun ω => z i ω*z j ω := by funext ω; rfl
      rw [hfun] at hh
      rw [integral_independent_centered_pair (dropoutNoise_independent hind p) hzm hzmean] at hh
      simp only [z, dropoutNoise_variance p (hq _ (hA i)) (hprob i) hp] at hh
      exact hh
    have hYinner (i j : e) : Integrable (fun ω => ⟪Y i ω, Y j ω⟫) μ :=
      integrable_inner_of_memLp_two (hY2 i) (hY2 j)
    have hscalarint (i j : e) : Integrable
        (fun ω => (z i ω*z j ω)*⟪V i ω, V j ω⟫) μ := by
      convert hYinner i j using 1
      funext ω
      simp only [Y, real_inner_smul_left, real_inner_smul_right]
      ring
    have hscalarcond (i j : e) :
        μ[fun ω => (z i ω*z j ω)*⟪V i ω, V j ω⟫ | m] =ᵐ[μ]
          (fun ω => (if i = j then p/(1-p) else 0)*⟪V i ω, V j ω⟫) := by
      have hh := condExp_mul_of_aestronglyMeasurable_right
        ((hV i).inner (hV j)).aestronglyMeasurable (hscalarint i j) (hzi i j)
      have hfun : ((fun ω => z i ω*z j ω) * (fun ω => ⟪V i ω,V j ω⟫)) =
          (fun ω => (z i ω*z j ω)*⟪V i ω,V j ω⟫) := by funext ω; rfl
      rw [hfun] at hh
      filter_upwards [hh, hpaircond i j] with ω hh hp
      change μ[fun ω => (z i ω*z j ω)*⟪V i ω,V j ω⟫ | m] ω =
        μ[fun ω => z i ω*z j ω | m] ω * ⟪V i ω,V j ω⟫ at hh
      rw [hp] at hh
      exact hh
    have heq : (fun ω => ‖∑ i, z i ω • V i ω‖^2) =
        ∑ i, ∑ j, (fun ω => (z i ω*z j ω)*⟪V i ω, V j ω⟫) := by
      funext ω
      simp only [Finset.sum_apply]
      rw [← real_inner_self_eq_norm_sq]
      simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    have houter := condExp_finsetSum (s := Finset.univ)
      (f := fun i => ∑ j, (fun ω => (z i ω*z j ω)*⟪V i ω,V j ω⟫))
      (fun i _ => integrable_finsetSum' Finset.univ (fun j _ => hscalarint i j)) m
    have hinner (i : e) := condExp_finsetSum (s := Finset.univ)
      (fun j _ => hscalarint i j) m
    filter_upwards [houter, ae_all_iff.mpr hinner,
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (hscalarcond i))] with ω ho hi hp
    rw [ho]
    simp only [Finset.sum_apply]
    simp_rw [hi]
    simp only [Finset.sum_apply]
    simp_rw [hp]
    simp only [ite_mul, zero_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
    · intro j _ hji
      rw [ite_eq_right (fun hij => hji hij.symm)]
    · simp

section Graph
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- One edge response after a deterministic output operator. -/
def gossipEdgeResponse (w : ℝ) (b : d → ℝ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d :=
  (w • innerSL ℝ (WithLp.toLp 2 b)).smulRight (T (WithLp.toLp 2 b))

omit [DecidableEq d] in
theorem gossipEdgeResponse_apply (w : ℝ) (b : d → ℝ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) (v : EuclideanSpace ℝ d) :
    gossipEdgeResponse w b T v =
      (w*dotProduct b (WithLp.ofLp v)) • T (WithLp.toLp 2 b) := by
  simp [gossipEdgeResponse, EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]

omit [DecidableEq d] [DecidableEq e] in
/-- Random L² states produce L² dropout errors; independence is unnecessary for
this integrability fact. -/
theorem gossipOracleNoise_memLp (p : ℝ) (A : e → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (w : e → ℝ) (b : e → d → ℝ)
    (v : Ω → EuclideanSpace ℝ d) (hv2 : MemLp v 2 μ) :
    MemLp (fun ω => gossipOracleNoise p A w b (WithLp.ofLp (v ω)) ω) 2 μ := by
  let Id : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d := ContinuousLinearMap.id ℝ _
  have hsum : MemLp (fun ω => ∑ i, dropoutNoise p (A i) ω •
      gossipEdgeResponse (w i) (b i) Id (v ω)) 2 μ := by
    apply memLp_finsetSum
    intro i _
    exact (dropoutNoise_memLp_top p (hA i)).smul
      (hv2.continuousLinearMap_comp (gossipEdgeResponse (w i) (b i) Id))
  convert hsum using 1
  funext ω
  simp only [gossipOracleNoise_eq, gossipEdgeResponse_apply, Id, ContinuousLinearMap.id_apply]

omit [DecidableEq d] [DecidableEq e] in
/-- Measurability of a state-dependent edge error uses only measurability of the
current state and edge events in the stated sigma-algebra. -/
theorem gossipOracleNoise_stronglyMeasurable (p : ℝ) (A : e → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (w : e → ℝ) (b : e → d → ℝ)
    (v : Ω → EuclideanSpace ℝ d) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun ω => gossipOracleNoise p A w b (WithLp.ofLp (v ω)) ω) := by
  let Id : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d := ContinuousLinearMap.id ℝ _
  have hh : StronglyMeasurable (fun ω => ∑ i, dropoutNoise p (A i) ω •
      gossipEdgeResponse (w i) (b i) Id (v ω)) := by
    have he : (fun ω => ∑ i, dropoutNoise p (A i) ω •
        gossipEdgeResponse (w i) (b i) Id (v ω)) =
        ∑ i, (fun ω => dropoutNoise p (A i) ω • gossipEdgeResponse (w i) (b i) Id (v ω)) := by
      funext ω
      simp
    rw [he]
    apply Finset.stronglyMeasurable_sum
    intro i _
    exact ((dropoutNoise_measurable p (hA i)).stronglyMeasurable).smul
      ((gossipEdgeResponse (w i) (b i) Id).continuous.comp_stronglyMeasurable hv)
  convert hh using 1
  funext ω
  simp only [gossipOracleNoise_eq, gossipEdgeResponse_apply, Id, ContinuousLinearMap.id_apply]

omit [DecidableEq d] in
/-- Exact conditional gossip covariance at a random L² current state. The edge
events are mutually independent and their sigma-algebra is independent of the
past; the displayed centering and covariance are conclusions. -/
theorem gossipOracleNoise_conditional_moments (p : ℝ) (hp : p < 1)
    (m q : MeasurableSpace Ω) (hm : m ≤ mΩ) (hq : q ≤ mΩ)
    (hfresh : Indep q m μ) (A : e → Set Ω)
    (hA : ∀ i, MeasurableSet[q] (A i)) (hind : iIndepSet A μ)
    (hprob : ∀ i, μ.real (A i) = 1-p)
    (w : e → ℝ) (b : e → d → ℝ)
    (v : Ω → EuclideanSpace ℝ d) (hv : StronglyMeasurable[m] v) (hv2 : MemLp v 2 μ)
    (T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d) :
    μ[fun ω => T (gossipOracleNoise p A w b (WithLp.ofLp (v ω)) ω) | m] =ᵐ[μ] 0 ∧
    μ[fun ω => ‖T (gossipOracleNoise p A w b (WithLp.ofLp (v ω)) ω)‖^2 | m] =ᵐ[μ]
      (fun ω => p/(1-p)*∑ i, (w i)^2*(dotProduct (b i) (WithLp.ofLp (v ω)))^2*
        ‖T (WithLp.toLp 2 (b i))‖^2) := by
  let : MeasurableSpace Ω := mΩ
  let V := fun i ω => gossipEdgeResponse (w i) (b i) T (v ω)
  have hV (i : e) : StronglyMeasurable[m] (V i) :=
    (gossipEdgeResponse (w i) (b i) T).continuous.comp_stronglyMeasurable hv
  have hV2 (i : e) : MemLp (V i) 2 μ :=
    hv2.continuousLinearMap_comp (gossipEdgeResponse (w i) (b i) T)
  have hh := dropout_sum_conditional_moments p hp m q hm hq hfresh A hA hind hprob V hV hV2
  have hnoise : (fun ω => T (gossipOracleNoise p A w b (WithLp.ofLp (v ω)) ω)) =
      (fun ω => ∑ i, dropoutNoise p (A i) ω • V i ω) := by
    funext ω
    simp only [gossipOracleNoise_eq, map_sum, map_smul, V, gossipEdgeResponse_apply]
  have hnoisepoint (ω : Ω) : T (gossipOracleNoise p A w b (WithLp.ofLp (v ω)) ω) =
      ∑ i, dropoutNoise p (A i) ω • V i ω := congrFun hnoise ω
  simp_rw [hnoisepoint]
  constructor
  · exact hh.1
  · refine hh.2.trans ?_
    apply Eventually.of_forall
    intro ω
    change p/(1-p)*(∑ i, ‖V i ω‖^2) = p/(1-p)*
      (∑ i, (w i)^2*(dotProduct (b i) (WithLp.ofLp (v ω)))^2*‖T (WithLp.toLp 2 (b i))‖^2)
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show V i ω = (w i*dotProduct (b i) (WithLp.ofLp (v ω))) •
        T (WithLp.toLp 2 (b i)) from gossipEdgeResponse_apply _ _ _ _]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]

end Graph

end
end chebyshev1.Stochastic
