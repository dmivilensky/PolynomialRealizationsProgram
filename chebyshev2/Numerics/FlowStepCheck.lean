import chebyshev2.Numerics.FlowRange

/-!
Article: chebyshev2, Lemma 21.
`chebyshev2.Numerics.FlowStep.check_sound` combines tube, coefficient, Taylor and
signed-stability checks into a sound endpoint bound.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.flowChainCheck_sound`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set LeanCert.Core
set_option autoImplicit false
noncomputable section

/--
Membership in the specified domain/enclosure: `y (a+W.width)∈W.output`.

Use: `chebyshev2.Numerics.ReferenceJetSource.actual_filter_step` uses this assertion to
establish membership in the specified domain/enclosure: `(referenceData R).normalizedFilter (σ
:= (sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Article: chebyshev2, Lemma 21.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Numerics.intervalSubsetCheck_sound`,
`chebyshev2.Numerics.FlowStep.check_range_sound` with the arguments shown in the proof.
-/
theorem FlowStep.check_sound (W : FlowStep) (hcheck : W.check=true)
    {C A B y : ℝ → ℝ} {a : ℝ}
    (hC : ContDiffOn ℝ (W.order+1) C (Icc a (a+W.width)))
    (hA : ContDiffOn ℝ (W.order+1) A (Icc a (a+W.width)))
    (hB : ContDiffOn ℝ (W.order+1) B (Icc a (a+W.width)))
    (hpoint : ∀ j<W.order,
      normalizedWithin C (Icc a (a+W.width)) j a∈jetAt W.pointC j ∧
      normalizedWithin A (Icc a (a+W.width)) j a∈jetAt W.pointA j ∧
      normalizedWithin B (Icc a (a+W.width)) j a∈jetAt W.pointB j)
    (hwhole : ∀ t∈Icc a (a+W.width),∀ j<W.order+1,
      normalizedWithin C (Icc a (a+W.width)) j t∈jetAt W.wholeC j ∧
      normalizedWithin A (Icc a (a+W.width)) j t∈jetAt W.wholeA j ∧
      normalizedWithin B (Icc a (a+W.width)) j t∈jetAt W.wholeB j)
    (hy : ContinuousOn y (Icc a (a+W.width)))
    (hyd : ∀ t∈Ioo a (a+W.width),HasDerivAt y (C t+A t*y t+B t*y t^2) t)
    (hy0 : y a∈W.initial) : y (a+W.width)∈W.output := by
  -- Use the identities/estimates `chebyshev2.Numerics.intervalSubsetCheck_sound`,
  -- `chebyshev2.Numerics.FlowStep.check_range_sound` with the arguments shown in the
  -- proof.
  have hp := hcheck
  simp only [FlowStep.check,Bool.and_eq_true,decide_eq_true_eq] at hp
  have hh : 0<(W.width:ℝ) := by exact_mod_cast hp.1.1.1.1.1
  apply intervalSubsetCheck_sound hp.2
  exact W.check_range_sound hcheck ⟨hC,hA,hB,hpoint,hwhole⟩ hy hyd hy0
    ⟨hh.le,le_rfl⟩ (IntervalRat.mem_singleton W.width)

end
end chebyshev2.Numerics
