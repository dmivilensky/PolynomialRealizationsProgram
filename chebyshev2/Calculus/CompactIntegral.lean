import chebyshev2.Calculus.ClosedInterval
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact

/-!
Article: chebyshev2, Theorem 3.2.
Differentiation and all-order regularity of parameter integrals on closed rectangles.
Use: `chebyshev2.Calculus.contDiffOn_compact_integral_of_derivatives` feeds
`chebyshev2.Calculus.cubicIntegral_smooth` (cubic Integral smooth).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` —
chebyshev2, Theorem 3.2; Constructed contact potential and calibrated reference.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {a b c d : ℝ} {F G : ℝ → ℝ → ℝ}

 /--
Continuity on the stated domain: `ContinuousOn (fun t => ∫ v in Icc c d, F t v) (Icc a b)`.

Use: `chebyshev2.Calculus.contDiffOn_compact_integral_of_derivatives` uses this continuity
result to prove the quantified assertion `∀ j, ContDiffOn ℝ ∞ (fun t
=> ∫ v in Icc c d, F j t v) (Icc a b)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation. Intersect the eventual or
almost-everywhere hypotheses, then prove the asserted relation at an arbitrary point in that
intersection.
-/
theorem continuousOn_compact_integral
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (fun t => ∫ v in Icc c d, F t v) (Icc a b) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF
  -- Establish continuity hslice before using the function at limits or in calculus arguments.
  have hslice (t : ℝ) (ht : t ∈ Icc a b) : ContinuousOn (F t) (Icc c d) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hv => ⟨ht,hv⟩)
  intro t ht
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hslice u hu).aestronglyMeasurable measurableSet_Icc
  · filter_upwards [self_mem_nhdsWithin] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact hM (u,v) ⟨hu,hv⟩
  · exact integrableOn_const (by simp) 
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact ((hF (t,v) ⟨ht,hv⟩).comp (f := fun u : ℝ => (u,v))
      (continuousWithinAt_id.prodMk continuousWithinAt_const)
      (fun _ hu => ⟨hu,hv⟩)).tendsto

 /--
Establishes the uniform, quantified assertion `∀ t ∈ Icc a b, HasDerivWithinAt (fun t => ∫ v in
Icc c d, F t v) (∫ v in Icc c d, G t v) (Icc a b) t`.

Use: `chebyshev2.Calculus.contDiffOn_compact_integral_of_derivatives` uses this identity to
establish establishes the uniform, quantified assertion `∀ j, ContDiffOn ℝ ∞ (fun t => ∫ v in
Icc c d, F j t v) (Icc a b)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem hasDerivWithinAt_compact_integral (hab : a<b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hd : ∀ t ∈ Ioo a b, ∀ v ∈ Icc c d, HasDerivAt (fun t => F t v) (G t v) t) :
    ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => ∫ v in Icc c d, F t v)
      (∫ v in Icc c d, G t v) (Icc a b) t := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply hasDerivWithinAt_Icc_of_continuous_derivative hab
    (continuousOn_compact_integral hF) (continuousOn_compact_integral hG)
  intro t ht
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  -- Establish continuity hsliceF before using the function at limits or in calculus arguments.
  have hsliceF : ContinuousOn (F t) (Icc c d) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hv => ⟨⟨ht.1.le,ht.2.le⟩,hv⟩)
  -- Establish continuity hsliceG before using the function at limits or in calculus arguments.
  have hsliceG : ContinuousOn (G t) (Icc c d) :=
    hG.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hv => ⟨⟨ht.1.le,ht.2.le⟩,hv⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo a b) (bound := fun _ => M) (isOpen_Ioo.mem_nhds ht) ?_
    (hsliceF.integrableOn_compact isCompact_Icc) (hsliceG.aestronglyMeasurable measurableSet_Icc)
    ?_ (integrableOn_const (by simp)) ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact (hF.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hv => ⟨⟨hu.1.le,hu.2.le⟩,hv⟩)).aestronglyMeasurable measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv u hu
    exact hM (u,v) ⟨⟨hu.1.le,hu.2.le⟩,hv⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv u hu
    exact hd u hu v hv

 /--
Establishes the uniform, quantified assertion `∀ j, ContDiffOn ℝ ∞ (fun t => ∫ v in Icc c d, F
j t v) (Icc a b)`.

Use: `chebyshev2.Calculus.cubicIntegral_smooth` uses this identity to establish establishes
the uniform, quantified assertion `∀ j, ContDiffOn ℝ ∞ (cubicIntegral D j) (Icc 0 β)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Induct on `k`; the recursive step uses the previous-stage assertion.
-/
theorem contDiffOn_compact_integral_of_derivatives (hab : a<b)
    (F : ℕ → ℝ → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hd : ∀ j, ∀ t ∈ Ioo a b, ∀ v ∈ Icc c d,
      HasDerivAt (fun t => F j t v) (F (j+1) t v) t) :
    ∀ j, ContDiffOn ℝ ∞ (fun t => ∫ v in Icc c d, F j t v) (Icc a b) := by
  -- Induct on `k`; the recursive step uses the previous-stage assertion.
  have hdiff j := hasDerivWithinAt_compact_integral hab (hc j) (hc (j+1)) (hd j)
  have hfinite : ∀ k : ℕ, ∀ j, ContDiffOn ℝ k (fun t => ∫ v in Icc c d, F j t v) (Icc a b) := by
    intro k
    induction k with
    | zero => exact fun j => contDiffOn_zero.mpr (continuousOn_compact_integral (hc j))
    | succ k ih =>
      intro j
      rw [show ((k+1:ℕ):ℕ∞ω)=(k:ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
      refine ⟨fun t ht => (hdiff j t ht).differentiableWithinAt,by simp,?_⟩
      exact (ih (j+1)).congr (fun t ht =>
        (hdiff j t ht).derivWithin (uniqueDiffOn_Icc hab t ht))
  intro j
  exact contDiffOn_infty.mpr (fun k => hfinite k j)

end
end chebyshev2.Calculus
