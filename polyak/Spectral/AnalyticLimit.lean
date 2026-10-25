import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Topology.ContinuousMap.Compact

/-!
Article: Appendix A, finite-support lemma, analytic limiting dual symbols.
Use: compact convex limits preserve holomorphy on an interior neighborhood;
a nonzero analytic symbol has finitely many zeros on a compact interval.
Proof: total boundedness of convex hulls, Weierstrass and isolated zeros.
-/

namespace polyak.Spectral
noncomputable section
open Set Filter
open scoped Topology

/-- Article: compactness of normalized dual combinations in a Banach function space. -/
theorem isCompact_closure_convexHull {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {s : Set E} (hs : IsCompact s) :
    IsCompact (closure (convexHull ℝ s)) := by
  exact isCompact_iff_totallyBounded_isComplete.mpr
    ⟨hs.totallyBounded.convexHull.closure,isClosed_closure.isComplete⟩

/-- Article: interior extension of a continuous function on the compact complex window.
Use: values outside the window play no part in differentiability on its interior. -/
def windowExtension {K : Set ℂ} (f : C(K,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ K then f ⟨z,hz⟩ else 0

/-- Article: the extension agrees with every sampled value on the compact window. -/
theorem windowExtension_coe {K : Set ℂ} (f : C(K,ℂ)) (z : K) :
    windowExtension f z = f z := by simp [windowExtension]

variable {K : Set ℂ} [CompactSpace K]

/-- Article: convergence in the continuous-function norm controls the interior extensions. -/
theorem tendstoUniformlyOn_windowExtension {f : ℕ → C(K,ℂ)} {g : C(K,ℂ)}
    (h : Tendsto f atTop (𝓝 g)) :
    TendstoUniformlyOn (fun n => windowExtension (f n)) (windowExtension g) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.mp h).eventually (gt_mem_nhds hε)] with n hn z hz
  have he := (f n-g).norm_coe_le_norm ⟨z,hz⟩
  simp only [ContinuousMap.sub_apply] at he
  rw [norm_sub_rev] at he
  simpa only [windowExtension, dite_eq_left hz, dist_eq_norm, ContinuousMap.sub_apply] using he.trans_lt hn

/-- Article: the class of holomorphic interior restrictions is closed under uniform limits. -/
theorem isClosed_holomorphic_window :
    IsClosed {f : C(K,ℂ) | DifferentiableOn ℂ (windowExtension f) (interior K)} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f g hf hg
  have hconv := (tendstoUniformlyOn_windowExtension hg).mono interior_subset
  exact hconv.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hf) isOpen_interior

omit [CompactSpace K] in
/-- Article: convex normalized combinations retain holomorphy. -/
theorem convex_holomorphic_window :
    Convex ℝ {f : C(K,ℂ) | DifferentiableOn ℂ (windowExtension f) (interior K)} := by
  intro f hf g hg a b _ha _hb _hab
  have he : windowExtension (a • f+b • g) =
      fun z => (a : ℂ)*windowExtension f z+(b : ℂ)*windowExtension g z := by
    funext z
    by_cases hz : z ∈ K <;> simp [windowExtension, hz, Complex.real_smul]
  change DifferentiableOn ℂ (windowExtension (a • f+b • g)) (interior K)
  rw [he]
  exact (hf.const_mul _).add (hg.const_mul _)

/-- Article: a compact convex limit of entire lag symbols is holomorphic in the window. -/
theorem holomorphic_of_mem_closure_convexHull {s : Set C(K,ℂ)} {f : C(K,ℂ)}
    (hs : ∀ g ∈ s, DifferentiableOn ℂ (windowExtension g) (interior K))
    (hf : f ∈ closure (convexHull ℝ s)) :
    DifferentiableOn ℂ (windowExtension f) (interior K) := by
  exact (closure_minimal (convex_holomorphic_window.convexHull_subset_iff.mpr hs)
    isClosed_holomorphic_window) hf

/-- Article: finite zeros of a nontrivial limiting dual symbol.
Use: all optimal measures are confined to this same finite set. -/
theorem finite_zeros_on_compact {U S : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hS : IsCompact S) (hSU : S ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hz : z ∈ U) (hnez : f z ≠ 0) :
    {w ∈ S | f w = 0}.Finite := by
  have ha := hf.analyticOnNhd hU
  have he := ha.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn
  have hnot : ¬ EqOn f 0 U := by
    intro h
    exact hnez (h hz)
  have hdisc := he.resolve_left hnot
  have hd : {w | f w ≠ 0} ∈ codiscreteWithin S :=
    (Filter.codiscreteWithin_mono hSU) hdisc
  convert hS.finite_sdiff_of_mem_codiscreteWithin hd using 1
  ext w
  simp

end
end polyak.Spectral
