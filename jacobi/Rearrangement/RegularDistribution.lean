import jacobi.Rearrangement.RegularIntegrals
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
The limiting regular orbit preserves the entire distribution of density
values, not only its mass and energy. Continuous test functions identify the
pushforward of the finite interval measure. Evaluating this actual measure
identity on half-lines proves equality of all strict superlevel measures.
Source: uniqueness of finite Borel measures from bounded continuous integrals, in mathlib.
Use: continuous distribution tests can have arbitrary values at zero on the finite interval.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The orbit closure preserves interval integrals of all continuous functions of the density.
Use: continuous distribution tests can have arbitrary values at zero on the finite interval.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: subtract the test function's value at zero, apply the proved whole-line
invariance, and restore the same constant integral on both finite intervals. -/
theorem regularOrbit_integral_interval {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    (hgr : g ∈ regularFamily R C K) {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in Icc (-R) R, F (g x))=∫ x in Icc (-R) R, F (f x) := by
  -- Subtracting F(0) makes the global integrand compactly supported without changing distribution information.
  let H (y : ℝ) := F y-F 0
  have h0 : H 0=0 := sub_self _
  have h := regularOrbit_integral_comp hf hg (F := H) (hF.sub continuous_const) h0
  rw [regular_integral_interval hgr h0,regular_integral_interval hf h0] at h
  have hfi : IntegrableOn (fun x => F (f x)) (Icc (-R) R) :=
    (hF.comp f.continuous).continuousOn.integrableOn_compact isCompact_Icc
  have hgi : IntegrableOn (fun x => F (g x)) (Icc (-R) R) :=
    (hF.comp g.continuous).continuousOn.integrableOn_compact isCompact_Icc
  have hi : IntegrableOn (fun _ : ℝ => F 0) (Icc (-R) R) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  dsimp only [H] at h
  rw [integral_sub hgi hi,integral_sub hfi hi] at h
  linarith

/-- The actual distribution measures on the common finite interval are equal.
Use: derives all superlevel identities and arbitrary Borel integral identities for the regular rearrangement.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: finite Borel measures on the real line are determined by bounded
continuous test integrals, which the compact regular orbit preserves exactly. -/
theorem regularOrbit_distribution {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    (hgr : g ∈ regularFamily R C K) :
    Measure.map g (volume.restrict (Icc (-R) R))=
      Measure.map f (volume.restrict (Icc (-R) R)) := by
  -- Both mapped measures are finite because the physical support interval has finite volume.
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map g.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable,
    integral_map f.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  exact regularOrbit_integral_interval hf hg hgr F.continuous

/-- Every strict superlevel measure is exactly preserved in the actual closed regular orbit.
Use: identifies the constructed radial limit as an equimeasurable rearrangement, rather than a weaker replacement.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: for nonnegative levels, superlevel sets lie in the common interval and
the distribution-measure identity applies. Negative levels give the whole line on both sides. -/
theorem regularOrbit_superlevel {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    (hgr : g ∈ regularFamily R C K) (t : ℝ) :
    volume {x | t < g x}=volume {x | t < f x} := by
  -- Testing the pushforward measure proves the full distribution statement, including level zero.
  by_cases ht : 0 ≤ t
  · have hsub (q : ℝ →ᵇ ℝ) (hq : q ∈ regularFamily R C K) :
        {x | t < q x} ⊆ Icc (-R) R := by
      intro x hx
      by_contra h
      have hz := regular_zero_compl hq h
      change t < q x at hx
      linarith
    have h := congrArg (fun μ : Measure ℝ => μ (Ioi t)) (regularOrbit_distribution hf hg hgr)
    rw [Measure.map_apply g.continuous.measurable measurableSet_Ioi,
      Measure.map_apply f.continuous.measurable measurableSet_Ioi,
      Measure.restrict_apply (g.continuous.measurable measurableSet_Ioi),
      Measure.restrict_apply (f.continuous.measurable measurableSet_Ioi)] at h
    exact (by simpa only [preimage,mem_Ioi,inter_eq_self_of_subset_left (hsub g hgr),
      inter_eq_self_of_subset_left (hsub f hf)] using h)
  · have hfg (q : ℝ →ᵇ ℝ) (hq : q ∈ regularFamily R C K) : {x | t < q x}=univ := by
      ext x
      simp only [mem_ofPred_eq,mem_univ,iff_true]
      exact (lt_of_not_ge ht).trans_le (hq.2.1 x).1
    rw [hfg g hgr,hfg f hf]

end
end jacobi.Rearrangement
