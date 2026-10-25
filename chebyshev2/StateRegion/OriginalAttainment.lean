import chebyshev2.StateRegion.ArticleRange

/-!
Article: chebyshev2, Proposition 7.
The compact image definition is literally the union printed in Proposition 7.
Use: `chebyshev2.StateRegion.Scales.states_iff` feeds `chebyshev2.HalfLine.state_mem`
(Proposition 7 for the literal ODE state and the actual density parameter).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.StateRegion.Scales
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
variable (S : Scales)

/--
An actual measure for the three integrands in equation (22).

Use: `chebyshev2.StateRegion.Scales.normalized_iff_original` uses this record of data and
proof obligations to prove the equivalence `(u,v,theta) ∈
S.normalized ↔ Nonempty (S.OriginalWitness u v theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
structure OriginalWitness (u v theta : ℝ) where
  /-- Probability measure realizing the original three state observations. -/
  measure : Measure ℝ
  /-- Total measure mass is one. -/
  probability : IsProbabilityMeasure measure
  /-- The realizing measure is supported on [0,1] up to a null set. -/
  supported : ∀ᵐ z ∂measure, z ∈ Icc (0:ℝ) 1
  /-- Its first response moment equals u. -/
  first : (∫ z, S.response S.a z ∂measure)=u
  /-- Its second response moment equals v. -/
  second : (∫ z, S.response S.b z ∂measure)=v
  /-- Its coordinate mean equals theta. -/
  third : (∫ z, z ∂measure)=theta

attribute [instance] OriginalWitness.probability

/--
The precise assertion is `Nonempty (S.OriginalWitness u v theta)`.

Use: `chebyshev2.StateRegion.Scales.normalized_iff_original` uses this assertion to
establish equivalence of the displayed criteria: `(u,v,theta) ∈ S.normalized ↔ Nonempty
(S.OriginalWitness u v theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem original_attainment {u v theta : ℝ} (W : MomentWitness S u v theta) :
    Nonempty (S.OriginalWitness u v theta) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let μ := Measure.map S.change W.measure
  have hμ : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff S.change_measurable.aemeasurable).mpr inferInstance
  refine ⟨⟨μ,hμ,S.mapped_supported W.supported,?_,?_,?_⟩⟩
  · have hm : Measurable (S.response S.a) := by unfold response; fun_prop
    rw [integral_map S.change_measurable.aemeasurable hm.aestronglyMeasurable]
    calc
      _ = ∫ w, w ∂W.measure := integral_congr_ae (W.supported.mono (fun w hw => by
        change S.change (S.change w)=w
        exact S.change_involution hw))
      _ = u := W.mean
  · have hm : Measurable (S.response S.b) := by unfold response; fun_prop
    rw [integral_map S.change_measurable.aemeasurable hm.aestronglyMeasurable]
    calc
      _ = ∫ w, S.f w ∂W.measure := integral_congr_ae (W.supported.mono (fun w hw => by
        have h := S.f_change (S.change_mem hw)
        rw [S.change_involution hw] at h
        exact h.symm))
      _ = v := W.second
  · change (∫ z, z ∂Measure.map S.change W.measure)=theta
    rw [integral_map S.change_measurable.aemeasurable
      (show AEStronglyMeasurable (fun z : ℝ => z) μ from measurable_id.aestronglyMeasurable)]
    calc
      _ = ∫ w, 1-S.g w ∂W.measure := integral_congr_ae (W.supported.mono (fun w hw => by
        have h := S.change_add_g hw
        linarith))
      _ = 1-(∫ w, S.g w ∂W.measure) := by
        rw [integral_sub (integrable_const _) (S.g_integrable W.supported)]
        simp
      _ = theta := W.third

/--
Exact range in the original spectral coordinate, including z=0 and z=1.

Equivalence of the displayed criteria: `(u,v,theta) ∈ S.normalized ↔ Nonempty
(S.OriginalWitness u v theta)`.

Use: `chebyshev2.StateRegion.Scales.states_iff` uses this assertion to establish
equivalence of the displayed criteria: `p ∈ S.states ↔ p=(0,0,0,0) ∨ ∃ q ∈ Ioc (0:ℝ) 2, ∃ u v
theta : ℝ, Nonempty (S.OriginalWitness u v theta) ∧ p=(q,q*u/S.k,q*v/S.k,q*theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.StateRegion.Scales.normalized_iff_attained`,
`chebyshev2.StateRegion.Scales.original_attainment`,
`chebyshev2.StateRegion.Scales.original_moments_mem` with the arguments shown in the proof.
-/
theorem normalized_iff_original (u v theta : ℝ) :
    (u,v,theta) ∈ S.normalized ↔ Nonempty (S.OriginalWitness u v theta) := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.normalized_iff_attained`,
  -- `chebyshev2.StateRegion.Scales.original_attainment`,
  -- `chebyshev2.StateRegion.Scales.original_moments_mem` with the arguments shown in the
  -- proof.
  constructor
  · intro h
    obtain ⟨W⟩ := (S.normalized_iff_attained u v theta).mp h
    exact S.original_attainment W
  · rintro ⟨W⟩
    have h := S.original_moments_mem W.supported
    rw [W.first,W.second,W.third] at h
    exact h

/--
Membership in the specified domain/enclosure: `(0,0,0,0) ∈ S.states`.

Use: `chebyshev2.StateRegion.Scales.states_iff` uses this assertion to establish
equivalence of the displayed criteria: `p ∈ S.states ↔ p=(0,0,0,0) ∨ ∃ q ∈ Ioc (0:ℝ) 2, ∃ u v
theta : ℝ, Nonempty (S.OriginalWitness u v theta) ∧ p=(q,q*u/S.k,q*v/S.k,q*theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.normalized_iff_attained`
with the arguments shown in the proof.
-/
theorem zero_state_mem : (0,0,0,0) ∈ S.states := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.normalized_iff_attained`
  -- with the arguments shown in the proof.
  have h : (0,0,1) ∈ S.normalized := by
    apply (S.normalized_iff_attained 0 0 1).mpr
    refine ⟨⟨Measure.dirac 0,inferInstance,?_,?_,?_,?_⟩⟩
    · exact (ae_dirac_iff measurableSet_Icc).mpr ⟨le_rfl,zero_le_one⟩
    · simp
    · simp
    · simp
  refine ⟨(0,0,0,1),⟨⟨le_rfl,by norm_num⟩,h⟩,?_⟩
  simp [stateLift]

/--
The compact image definition is literally the union printed in Proposition 7.

Equivalence of the displayed criteria: `p ∈ S.states ↔ p=(0,0,0,0) ∨ ∃ q ∈ Ioc (0:ℝ) 2, ∃ u v
theta : ℝ, Nonempty (S.OriginalWitness u v theta) ∧ p=(q,q*u/S.k,q*v/S.k,q*theta)`.

Use: `chebyshev2.HalfLine.state_mem` uses this identity to establish membership in the
specified domain/enclosure: `Filters.state G x ∈ (stateScales G).states`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem states_iff {p : ℝ × ℝ × ℝ × ℝ} : p ∈ S.states ↔
    p=(0,0,0,0) ∨ ∃ q ∈ Ioc (0:ℝ) 2, ∃ u v theta : ℝ,
      Nonempty (S.OriginalWitness u v theta) ∧ p=(q,q*u/S.k,q*v/S.k,q*theta) := by
  -- Separate `q=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  constructor
  · rintro ⟨⟨q,u,v,theta⟩,⟨hq,hN⟩,hp⟩
    by_cases hz : q=0
    · left
      rw [← hp]
      simp [stateLift,hz]
    · right
      refine ⟨q,⟨lt_of_le_of_ne hq.1 (Ne.symm hz),hq.2⟩,u,v,theta,
        (S.normalized_iff_original u v theta).mp hN,hp.symm⟩
  · rintro (rfl | ⟨q,hq,u,v,theta,hW,rfl⟩)
    · exact S.zero_state_mem
    · exact ⟨(q,u,v,theta),⟨⟨hq.1.le,hq.2⟩,(S.normalized_iff_original u v theta).mpr hW⟩,rfl⟩

end
end chebyshev2.StateRegion.Scales
