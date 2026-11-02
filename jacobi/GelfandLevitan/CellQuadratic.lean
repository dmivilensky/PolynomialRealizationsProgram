import jacobi.Analysis.HalfCells
import jacobi.GelfandLevitan.KernelPairing

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The continuous GL quadratic form of actual finite step functions is
exactly a finite matrix of cell integrals. This justifies the comparison
between the uniformly approximating sampled kernels and the original
positive continuum operator, with the genuine physical Lebesgue measure.
Use: cellEmbedding_kernel expands the true original quadratic form into these entries; sampled-kernel errors can then be bounded cell by cell.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference jacobi.Analysis
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- A genuine continuous kernel integrated over two physical cells.
Use: cellEmbedding_kernel expands the true original quadratic form into
these entries; sampled-kernel errors can then be bounded cell by cell.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def cellKernelEntry (G : C(Interval×Interval,ℝ)) (S T : Set Interval) : ℝ :=
  ∫ p in S ×ˢ T, G p ∂(volume.prod volume)

/-- Pairing two actual unit-cell L2 indicators with a continuous kernel
gives its original double cell integral.
Use: cellEmbedding_kernel computes the finite compression of the real
continuum kernel without a point-evaluation identification assumption.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: use the actual almost-everywhere representatives on each factor
of the product measure. Their product is the rectangle indicator. -/
theorem cellKernelEntry_indicator (G : C(Interval×Interval,ℝ))
    {S T : Set Interval} (hs : MeasurableSet S) (ht : MeasurableSet T) :
    (∫ p:Interval×Interval,
      (indicatorConstLp (μ:=(volume : Measure Interval)) 2 hs (measure_ne_top _ _) (1:ℝ) p.1 *
       indicatorConstLp (μ:=(volume : Measure Interval)) 2 ht (measure_ne_top _ _) (1:ℝ) p.2)*G p ∂(volume.prod volume)) =
      cellKernelEntry G S T := by
  rw [cellKernelEntry,← integral_indicator (hs.prod ht)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=measure_ne_top _ _) (c:=(1:ℝ))),
    Measure.quasiMeasurePreserving_snd.ae
    (indicatorConstLp_coeFn (p:=2) (hs:=ht) (hμs:=measure_ne_top _ _) (c:=(1:ℝ)))] with p hp hq
  rw [hp,hq]
  by_cases hps : p.1∈S <;> by_cases hqt : p.2∈T <;> simp [hps,hqt]

/-- The full continuous-kernel pairing of two genuine finite cell
embeddings is its exact finite matrix of original cell integrals.
Use: the two source GL quadratic lower bounds become finite coefficient
inequalities with no hidden quadrature or operator premise.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: expand the actual finite step representatives on the two product
coordinates. Every scalar-weighted indicator pair is integrable by the
established L2 kernel bound. Commute only finite sums and integrals, then
evaluate each genuine indicator pairing by its true cell integral. -/
theorem cellEmbedding_kernel {ι : Type*} [Fintype ι]
    (S : ι→Set Interval) (hs : ∀ i, MeasurableSet (S i))
    (G : C(Interval×Interval,ℝ)) (v w : ι→ℝ) :
    (∫ p:Interval×Interval,
      (cellEmbedding (μ:=(volume : Measure Interval)) S hs (fun _ => measure_ne_top _ _) v p.1 *
       cellEmbedding (μ:=(volume : Measure Interval)) S hs (fun _ => measure_ne_top _ _) w p.2)*G p ∂(volume.prod volume)) =
      ∑ i, ∑ j, (v i*w j)*cellKernelEntry G (S i) (S j) := by
  -- Expand actual almost-everywhere representatives on both product-measure coordinates.
  classical
  let u (i:ι) : Space := indicatorConstLp (μ:=(volume : Measure Interval)) 2 (hs i) (measure_ne_top _ _) (1:ℝ)
  have hu (i:ι) : ⇑(u i) =ᵐ[volume] (S i).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hpair (i j:ι) : Integrable
      (fun p:Interval×Interval => (v i*w j)*((u i p.1*u j p.2)*G p)) (volume.prod volume) :=
    (continuousKernelPairing_integrable (u i) (u j) G).const_mul _
  have he : (fun p:Interval×Interval =>
      (cellEmbedding (μ:=(volume : Measure Interval)) S hs (fun _ => measure_ne_top _ _) v p.1 *
       cellEmbedding (μ:=(volume : Measure Interval)) S hs (fun _ => measure_ne_top _ _) w p.2)*G p) =ᵐ[volume.prod volume]
      fun p => ∑ i, ∑ j, (v i*w j)*((u i p.1*u j p.2)*G p) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (cellEmbedding_ae S hs _ v),
      Measure.quasiMeasurePreserving_snd.ae (cellEmbedding_ae S hs _ w),
      Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr hu),
      Measure.quasiMeasurePreserving_snd.ae (ae_all_iff.mpr hu)] with p hv hw h1 h2
    rw [hv,hw]
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [h1 i,h2 j]
    by_cases hi : p.1∈S i <;> by_cases hj : p.2∈S j <;>
      simp [hi,hj,mul_assoc,mul_comm]
  rw [integral_congr_ae he,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hpair i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hpair i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  congr 1
  exact cellKernelEntry_indicator G (hs i) (hs j)

/-- A continuous kernel that varies by at most delta across a cell
rectangle differs from its sampled constant integral by at most the
rectangle measure times delta.
Use: cell-average matrices approximate the actual uniformly sampled
GL kernels with an error small enough for finite-section coercivity.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: integrate the difference from the sampled constant over the
actual rectangle and apply the community integral norm bound. -/
theorem cellKernelEntry_error (G : C(Interval×Interval,ℝ))
    {S T : Set Interval} {c δ : ℝ}
    (hG : ∀ p∈S ×ˢ T, |G p-c|≤δ) :
    |cellKernelEntry G S T-
      (volume.real S*volume.real T)*c|≤(volume.real S*volume.real T)*δ := by
  -- Subtract the sampled constant inside the genuine rectangle integral.
  have hi : Integrable (fun p:Interval×Interval => G p) (volume.prod volume) :=
    G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : (volume.prod volume).real (S ×ˢ T)=volume.real S*volume.real T := by
    simp only [Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
  have he : cellKernelEntry G S T-(volume.real S*volume.real T)*c=
      ∫ p in S ×ˢ T, G p-c ∂(volume.prod volume) := by
    rw [integral_sub hi.integrableOn (integrable_const c),setIntegral_const,smul_eq_mul,hm]
    rfl
  rw [he]
  have hh := norm_setIntegral_le_of_norm_le_const
    (f:=fun p:Interval×Interval => G p-c) (C:=δ)
    (measure_lt_top (volume.prod volume) (S ×ˢ T))
    (fun p hp => by simpa only [Real.norm_eq_abs] using hG p hp)
  simpa only [Real.norm_eq_abs,hm,mul_comm δ] using hh

/-- The original GL quadratic form on a finite paired step function
is its exact cell-integrated finite quadratic form.
Use: cellGram_coercive compares both physical edge forms with the
actual original Gram matrix, without postulating an operator realization.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: substitute the established exact L2 cell norm and the genuine
finite double-integral expansion into the original source quadratic. -/
theorem halfCellVector_quadratic (a : ℝ) (ha : -1<a)
    {M : ℝ} (hM : 0<M) {L : ℕ} (hL : 4*(L:ℝ)≤M) (v : Fin L→ℝ) :
    quadratic a ha (halfCellVector M v) =
      (2/M)*(∑ l, (v l)^2) +
      ∑ i, ∑ j, cellKernelEntry (kernelMap a ha)
        (halfCell M i.val) (halfCell M j.val)*v i*v j := by
  -- Both terms are computed with the same original cell width and physical measure.
  unfold quadratic
  rw [halfCellVector_norm_sq hM hL]
  congr 1
  calc
    _ = ∑ i:Fin L, ∑ j:Fin L, (v i*v j)*cellKernelEntry (kernelMap a ha)
        (halfCell M i.val) (halfCell M j.val) :=
      cellEmbedding_kernel (fun l : Fin L => halfCell M l.val)
        (fun l => halfCell_measurable M l.val) (kernelMap a ha) v v
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end
end jacobi.GelfandLevitan
