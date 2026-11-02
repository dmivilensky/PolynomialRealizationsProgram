import jacobi.Rearrangement.RegularIntegrals
import jacobi.Rearrangement.SpectralPolarization

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
All finite exponential graph integrals increase on the compact regular
polarization orbit and its closure. Cycles identify these genuine integrals
with the actual operator's spectral moments; moment roots and the Fredholm
series give the top eigenvalue and the extended Fredholm comparison as well.
Source: polarization comparison, dominated convergence and the spectral trace formula.
Use: an integrable independent-coordinate majorant for graph integral convergence.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter jacobi.Variational
open scoped NNReal Topology BoundedContinuousFunction BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The compactly supported constant envelope of the regular density family.
Use: an integrable independent-coordinate majorant for graph integral convergence.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def regularEnvelope (R C : ℝ) : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => C)

/-- The common regular envelope is integrable on the real line.
Use: finite product Fubini supplies a majorant at every graph order.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: a constant is integrable on the finite-measure compact interval. -/
theorem regularEnvelope_integrable (R C : ℝ) : Integrable (regularEnvelope R C) :=
  (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc

/-- Every actual regular density is bounded in absolute value by the same integrable envelope.
Use: dominated convergence of graph integrands throughout the regular orbit closure.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: inside the interval use nonnegativity and the bound C; outside it both values vanish. -/
theorem regularEnvelope_bound {f : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (x : ℝ) : |f x| ≤ regularEnvelope R C x := by
  by_cases hx : x ∈ Icc (-R) R
  · simpa only [regularEnvelope,indicator_of_mem hx,abs_of_nonneg (hf.2.1 x).1] using (hf.2.1 x).2
  · simp only [regularEnvelope,indicator_of_notMem hx,regular_zero_compl hf hx,abs_zero,le_refl]

/-- Every finite graph integral is continuous on the actual regular family.
Use: the finite polarization inequality passes to the constructed radial limit at all cyclic orders.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: dominate each graph integrand by the finite product of the independent
compactly supported envelopes; products of evaluation maps are continuous. -/
theorem regular_graph_continuous {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (R C : ℝ) (K : ℝ≥0) :
    ContinuousOn (fun f : ℝ →ᵇ ℝ => ∫ z, graphIntegrand left right f z)
      (regularFamily R C K) := by
  -- Absolute convergence holds on the genuine product Lebesgue space, including repeated or closing edges.
  apply continuousOn_of_dominated (bound := fun z : V → ℝ => ∏ v, regularEnvelope R C (z v))
  · intro f _
    have hm : Measurable (graphIntegrand left right f) := by unfold graphIntegrand; fun_prop
    exact hm.aestronglyMeasurable
  · intro f hf
    exact Eventually.of_forall fun z => (graphIntegrand_bound left right f z).trans
      (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun v _ => regularEnvelope_bound hf (z v)))
  · exact Integrable.fintype_prod (fun _ => regularEnvelope_integrable R C)
  · apply Eventually.of_forall
    intro z
    apply Continuous.continuousOn
    unfold graphIntegrand
    fun_prop

/-- Simultaneous reflection through zero leaves every exponential graph integral unchanged.
Use: reflection can be included in the actual polarization orbit without weakening any spectral constraint.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: reflect every physical coordinate by the already proved measure-preserving
cube action; all exponential edge distances remain unchanged. -/
theorem graph_integral_mirror {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (f : ℝ →ᵇ ℝ) :
    (∫ z, graphIntegrand left right (mirrorBCF f) z)=∫ z, graphIntegrand left right f z := by
  -- The change of variables reflects every vertex together, preserving each edge length.
  have he (z : V → ℝ) : graphIntegrand left right (mirrorBCF f) z=
      graphIntegrand left right f (cubeReflection 0 (fun _ => 1) z) := by
    unfold graphIntegrand
    congr 1
    · apply Finset.prod_congr rfl
      intro v _
      change f (-z v)=f (reflect 0 (z v))
      simp only [reflect,mul_zero,zero_sub]
    · apply Finset.prod_congr rfl
      intro e _
      change exp (-|z (left e)-z (right e)|)=
        exp (-|reflect 0 (z (left e))-reflect 0 (z (right e))|)
      simp only [reflect,mul_zero,zero_sub,neg_sub_neg,abs_sub_comm]
  simp_rw [he]
  exact (cubeReflection_preserve 0 (fun _ : V => 1)).integral_comp' _

/-- Every finite orbit element increases every actual graph integral.
Use: establishes cyclic moment monotonicity before taking the compact orbit limit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: induction applies the proved graph polarization inequality to the actual
regular density at each step and exact invariance at a reflection step. -/
theorem RegularOrbit.graph_le {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hg : RegularOrbit f g) (hf : f ∈ regularFamily R C K) :
    (∫ z, graphIntegrand left right f z) ≤ ∫ z, graphIntegrand left right g z := by
  -- The comparison always concerns the literal density functions used to define the operator.
  induction hg with
  | base => exact le_refl _
  | @polarize q hq a _ ih =>
    exact ih.trans (graph_integral_polarize left right (regularDensity q (hq.regular hf)) a)
  | @mirror q _ ih =>
    rw [graph_integral_mirror left right q]
    exact ih

/-- Every member of the closed regular orbit increases every finite exponential graph integral.
Use: the actual radial limit satisfies all cyclic inequalities simultaneously.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: continuity makes the graph superlevel set closed relative to the closed
regular family, which contains the entire finite orbit. -/
theorem regularOrbit_graph_le {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q}) :
    (∫ z, graphIntegrand left right f z) ≤ ∫ z, graphIntegrand left right g z := by
  -- A single closure construction works for every graph; no graph-dependent choice of limit is made.
  have hc := (regular_graph_continuous left right R C K).preimage_isClosed_of_isClosed
    (regularFamily_closed R C K) (isClosed_Ici (a := ∫ z, graphIntegrand left right f z))
  have hi : {q | RegularOrbit f q} ⊆ regularFamily R C K ∩
      (fun q : ℝ →ᵇ ℝ => ∫ z, graphIntegrand left right q z) ⁻¹'
        Ici (∫ z, graphIntegrand left right f z) :=
    fun _ hq => ⟨hq.regular hf,hq.graph_le left right hf⟩
  exact (closure_minimal hi hc hg).2

/-- All positive integer moments of the actual kernel spectrum increase in the regular orbit closure.
Use: preserves every moment constraint at the constructed symmetric decreasing density.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: specialize the graph comparison to the closed cycle and apply the proved
multiple-integral trace formula to both actual densities. -/
theorem regularOrbit_moment_le {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    (hgr : g ∈ regularFamily R C K) (n : ℕ) :
    (∑' j, (regularDensity f hf).spectrum j^(n+1)) ≤
      ∑' j, (regularDensity g hgr).spectrum j^(n+1) := by
  -- Identification with the genuine operator spectrum excludes surrogate moment certificates.
  have h := regularOrbit_graph_le (cycleLeft n) (cycleRight n) hf hg
  simp_rw [cycle_graph] at h
  simp only [L1Source.spectrum]
  rw [jacobi.Continuum.moment_multiple_integral (regularDensity f hf).integrable
      (regularDensity f hf).measurable (regularDensity f hf).nonneg n,
    jacobi.Continuum.moment_multiple_integral (regularDensity g hgr).integrable
      (regularDensity g hgr).measurable (regularDensity g hgr).nonneg n]
  exact h

/-- The largest actual eigenvalue increases in the same regular orbit closure.
Use: the constructed radial replacement preserves the ground-state constraint as well.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: take positive integer roots of the proved moment comparisons and their proved spectral limits. -/
theorem regularOrbit_top_le {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    (hgr : g ∈ regularFamily R C K) :
    observe (regularDensity f hf) .top ≤ observe (regularDensity g hgr) .top := by
  -- Recover the top of the same spectrum used in every cyclic trace.
  let m := regularDensity f hf
  let q := regularDensity g hgr
  apply le_of_tendsto_of_tendsto (jacobi.Continuum.kernel_moment_root_limit m.integrable m.nonneg)
    (jacobi.Continuum.kernel_moment_root_limit q.integrable q.nonneg)
  exact Eventually.of_forall fun n => rpow_le_rpow
    (tsum_nonneg (fun j => pow_nonneg
      ((chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg j) _))
    (regularOrbit_moment_le hf hg hgr n) (by positivity)

/-- The extended Fredholm functional increases in the regular orbit closure, even at poles.
Use: the same radial replacement preserves the Fredholm relaxation's superlevel constraint.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: compare the nonnegative moment series term by term, using all proved cyclic moment inequalities. -/
theorem regularOrbit_fredholm_le {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    (hgr : g ∈ regularFamily R C K) {s : ℝ} (hs : 0 ≤ s) :
    (regularDensity f hf).fredholm s ≤ (regularDensity g hgr).fredholm s := by
  apply fredholm_mono_of_moments _ _ hs
  intro n
  simpa only [Nat.add_assoc] using regularOrbit_moment_le hf hg hgr (n+1)

end
end jacobi.Rearrangement
