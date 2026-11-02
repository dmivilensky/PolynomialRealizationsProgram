import jacobi.GelfandLevitan.CutoffFormula

/-!
Article: jacobi, Proposition C.2.
The genuine interval indicator changes pointwise away from one null
boundary point. Dominated convergence for the actual square-integrable
input proves strong continuity of P_t on the fixed original Hilbert
space. No operator-norm continuity of the projections is asserted.
Use: dominated convergence for the moving source indicator holds almost everywhere, including when t is an endpoint.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The original spatial coordinate equals any prescribed physical endpoint only on a genuine null set.
Use: dominated convergence for the moving source indicator holds almost everywhere, including when t is an endpoint.
Article: jacobi, Proposition C.2.
Source: nonatomic Lebesgue measure of a singleton.
Proof: the spatial coordinate is injective, so its level set is a subsingleton and has zero original Lebesgue measure. -/
theorem coordinate_ne_ae (t : ℝ) : ∀ᵐ s:Interval,(s:ℝ)≠t := by
  have hz : (volume : Measure Interval) {s | (s:ℝ)=t}=0 :=
    (show ({s:Interval | (s:ℝ)=t} : Set Interval).Subsingleton from
      fun _ hx _ hy => Subtype.ext (hx.trans hy.symm)).measure_zero volume
  simpa only [ae_iff,not_not] using hz

/-- The true squared distance between two projected source inputs is the literal integral of their indicator difference squared.
Use: reduces strong continuity of the genuine source projection to ordinary dominated convergence on original spatial functions.
Article: jacobi, Proposition C.2.
Proof: the original L2 norm square is its actual inner integral. Replace
the two genuine projections and their difference by the proved original
indicator representatives and use the real scalar inner product. -/
theorem cutoffProjection_dist_sq (v : halfSubspace) (t u : ℝ) :
    ‖cutoffProjection t v-cutoffProjection u v‖^2=
      ∫ s:Interval,((prefixSet t).indicator (v:Space) s-
        (prefixSet u).indicator (v:Space) s)^2 := by
  -- All norms here are the original Hilbert norms of the genuine zero-extended source inputs.
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ ((cutoffProjection t v:Space)-(cutoffProjection u v:Space))
    ((cutoffProjection t v:Space)-(cutoffProjection u v:Space))=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (cutoffProjection t v:Space) (cutoffProjection u v:Space),
    cutoffProjection_ae t v,cutoffProjection_ae u v] with s hs ht hu
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ht,hu,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- The genuine source cutoff projections depend strongly continuously on the physical endpoint.
Use: every original compressed rank-one kernel term varies continuously in operator norm; together with the actual summable majorant this gives continuity of A_t and of the GL solution rows.
Article: jacobi, Proposition C.2.
Proof: away from the single null boundary point, each actual indicator
is locally constant in the physical endpoint. Its squared difference
is bounded by the original integrable input square. Dominated convergence
makes the actual squared Hilbert distance tend to zero; continuity of
the real square root gives convergence in the genuine Hilbert norm. -/
theorem cutoffProjection_strong_continuous (v : halfSubspace) :
    Continuous (fun t:ℝ => cutoffProjection t v) := by
  -- Moving interval boundaries are handled on the original measure space; no uniform operator convergence of P_t is used.
  apply continuous_iff_continuousAt.mpr
  intro u
  let g := fun t:ℝ => fun s:Interval =>
    ((prefixSet t).indicator (v:Space) s-(prefixSet u).indicator (v:Space) s)^2
  have hg (t : ℝ) : AEStronglyMeasurable (g t) :=
    (((Lp.memLp (v:Space)).aestronglyMeasurable.indicator (prefixSet_measurable t)).sub
      ((Lp.memLp (v:Space)).aestronglyMeasurable.indicator (prefixSet_measurable u))).pow 2
  have hb (t : ℝ) (s : Interval) : ‖g t s‖≤(v:Space) s^2 := by
    dsimp [g]
    rw [abs_of_nonneg (sq_nonneg _)]
    by_cases ht : s∈prefixSet t <;> by_cases hu : s∈prefixSet u <;>
      simp only [indicator_of_mem,indicator_of_notMem,ht,hu,sub_zero,zero_sub,
        sub_self,neg_sq,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] <;>
      nlinarith [sq_nonneg ((v:Space) s)]
  have hl : ∀ᵐ s:Interval,Tendsto (fun t => g t s) (𝓝 u) (𝓝 0) := by
    filter_upwards [coordinate_ne_ae u] with s hs
    rcases lt_or_gt_of_ne hs with hsu | hus
    · have he : ∀ᶠ t:ℝ in 𝓝 u,s∈prefixSet t :=
        (eventually_gt_nhds hsu).mono (fun _ ht => ht.le)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with t ht
      have hu : s∈prefixSet u := hsu.le
      simp only [g,indicator_of_mem ht,indicator_of_mem hu,sub_self,zero_pow,
        ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
    · have he : ∀ᶠ t:ℝ in 𝓝 u,s∉prefixSet t :=
        (eventually_lt_nhds hus).mono (fun _ ht => not_le.mpr ht)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with t ht
      have hu : s∉prefixSet u := not_le.mpr hus
      simp only [g,indicator_of_notMem ht,indicator_of_notMem hu,
        sub_self,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  have hi := tendsto_integral_filter_of_dominated_convergence
    (fun s:Interval => (v:Space) s^2) (Eventually.of_forall hg)
    (Eventually.of_forall (fun t => Eventually.of_forall (hb t)))
    (Lp.memLp (v:Space)).integrable_sq hl
  have hs : Tendsto (fun t:ℝ => ‖cutoffProjection t v-cutoffProjection u v‖^2)
      (𝓝 u) (𝓝 0) := by
    simpa only [cutoffProjection_dist_sq,integral_zero] using hi
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun t:ℝ => Real.sqrt (‖cutoffProjection t v-cutoffProjection u v‖^2))
    (𝓝 u) (𝓝 (Real.sqrt 0)) at hh
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,dist_eq_norm] using hh

/-- The actual source cutoff action is jointly continuous in the physical endpoint and the genuine Hilbert input.
Use: a continuously moving original source row remains continuous after its physical cutoff, as required in the actual GL inverse construction.
Article: jacobi, Proposition C.2.
Source: joint continuity of uniformly Lipschitz maps with continuous parameter sections.
Proof: each original projection is one-Lipschitz in its genuine input and the true fixed-input endpoint sections are strongly continuous. Apply the community joint-continuity theorem. -/
theorem cutoffProjection_joint_continuous :
    Continuous (fun p:ℝ×halfSubspace => cutoffProjection p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun t => by
      change LipschitzWith (1:NNReal) (cutoffProjection t)
      exact ContinuousLinearMap.lipschitzWith_of_opNorm_le
        (f := cutoffProjection t) (K := 1) (cutoffProjection_norm_le t))
    cutoffProjection_strong_continuous

end
end jacobi.GelfandLevitan
