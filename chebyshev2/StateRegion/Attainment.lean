import chebyshev2.StateRegion.Mixtures

/-!
Article: chebyshev2, Proposition 7.
Proposition 12 and Lemma 8: exact equality of the compact rational region and the three-moment
range, including all boundary faces and attainment.
Use: `chebyshev2.StateRegion.Scales.normalized_iff_attained` feeds
`chebyshev2.StateRegion.Scales.normalized_iff_original` (Exact range in the original spectral
coordinate, including z=0 and z=1).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.StateRegion
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
A probability measure on [0,1] realizing the transformed mean, f moment and complementary g
moment. It is the constructive counterpart of the state-region inequalities.

Use: `chebyshev2.StateRegion.Scales.attain_interval` uses this record of data and proof
obligations to establish `Nonempty (MomentWitness S u (S.V u t)
theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
structure MomentWitness (S : Scales) (u v theta : ℝ) where
  /-- Probability measure realizing the transformed state coordinates. -/
  measure : Measure ℝ
  /-- Total measure mass is one. -/
  probability : IsProbabilityMeasure measure
  /-- The transformed realizing measure is supported on [0,1] up to a null set. -/
  supported : ∀ᵐ w ∂measure, w ∈ Icc (0:ℝ) 1
  /-- Its coordinate mean equals u. -/
  mean : (∫ w, w ∂measure)=u
  /-- Its f moment equals v. -/
  second : (∫ w, S.f w ∂measure)=v
  /-- One minus its g moment equals theta. -/
  third : 1-(∫ w, S.g w ∂measure)=theta

attribute [instance] MomentWitness.probability

namespace Scales
variable (S : Scales)

/--
The precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaPlus u t))`.

Use: `chebyshev2.StateRegion.Scales.attain_interval` uses this assertion to establish the
precise assertion is `Nonempty (MomentWitness S u (S.V u t) theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `u=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem attain_thetaPlus {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    Nonempty (MomentWitness S u (S.V u t) (S.thetaPlus u t)) := by
  -- Separate `u=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hu0 : u=0
  · subst u
    refine ⟨⟨Measure.dirac 0,inferInstance,?_,?_,?_,?_⟩⟩
    · exact (ae_dirac_iff measurableSet_Icc).mpr ⟨le_rfl,zero_le_one⟩
    · simp
    · simp [V]
    · simp [thetaPlus]
  · have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    let y := S.yMinus u t
    have hy : y ∈ Icc (0:ℝ) 1 :=
      ⟨hu.1.trans (S.yMinus_bounds hu ht).1,(S.yMinus_bounds hu ht).2⟩
    have hyp : 0 < y := hup.trans_le (S.yMinus_bounds hu ht).1
    have hp : u/y ∈ Icc (0:ℝ) 1 :=
      ⟨div_nonneg hu.1 hyp.le,(div_le_one hyp).mpr (S.yMinus_bounds hu ht).1⟩
    have hm := S.yMinus_moment hu ht
    refine ⟨⟨twoPoint (u/y) 0 y,twoPoint_probability hp,
      twoPoint_supported ⟨le_rfl,zero_le_one⟩ hy,?_,?_,?_⟩⟩
    · rw [twoPoint_integral hp]
      simp [div_mul_cancel₀ _ hyp.ne']
    · rw [twoPoint_integral hp,S.f_zero,mul_zero,zero_add]
      change u/y*(S.k₀*y/S.D y)=S.V u t
      calc
        _ = S.k₀*u/S.D y := by field_simp
        _ = S.V u t := (div_eq_iff (S.D_pos hy.2).ne').mpr (by simpa only [mul_comm] using hm.symm)
    · rw [twoPoint_integral hp,S.g_zero,mul_zero,zero_add]
      change 1-u/y*(S.k₀*y/S.E y)=1-S.k₀*u/S.E y
      field_simp

/--
The precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaMinus u t))`.

Use: `chebyshev2.StateRegion.Scales.attain_interval` uses this assertion to establish the
precise assertion is `Nonempty (MomentWitness S u (S.V u t) theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `u=1` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem attain_thetaMinus {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    Nonempty (MomentWitness S u (S.V u t) (S.thetaMinus u t)) := by
  -- Separate `u=1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hu1 : u=1
  · subst u
    refine ⟨⟨Measure.dirac 1,inferInstance,?_,?_,?_,?_⟩⟩
    · exact (ae_dirac_iff measurableSet_Icc).mpr ⟨zero_le_one,le_rfl⟩
    · simp
    · simp [V]
    · simp [thetaMinus]
  · have hul : u < 1 := lt_of_le_of_ne hu.2 hu1
    let y := S.yPlus u t
    have hyu := (S.yPlus_bounds hu ht).2
    have hy : y ∈ Icc (0:ℝ) 1 := ⟨(S.yPlus_bounds hu ht).1,hyu.trans hu.2⟩
    have hyp : 0 < 1-y := sub_pos.mpr (hyu.trans_lt hul)
    have hp : (u-y)/(1-y) ∈ Icc (0:ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hyu) hyp.le,(div_le_one hyp).mpr (by linarith [hu.2])⟩
    have hm := S.yPlus_moment hu ht
    refine ⟨⟨twoPoint ((u-y)/(1-y)) y 1,twoPoint_probability hp,
      twoPoint_supported hy ⟨zero_le_one,le_rfl⟩,?_,?_,?_⟩⟩
    · rw [twoPoint_integral hp]
      field_simp
      ring
    · rw [twoPoint_integral hp,S.f_one,mul_one]
      change (1-(u-y)/(1-y))*(S.k₀*y/S.D y)+(u-y)/(1-y)=S.V u t
      have hd := (S.D_pos hy.2).ne'
      field_simp
      dsimp [D,k₀,k₁] at hm ⊢
      dsimp only [y] at *
      linear_combination (1-S.yPlus u t)*hm
    · rw [twoPoint_integral hp,S.g_one,mul_one]
      change 1-((1-(u-y)/(1-y))*(S.k₀*y/S.E y)+(u-y)/(1-y))=S.k*(1-u)/S.E y
      have he := (S.E_pos hy.1).ne'
      field_simp
      dsimp [E,k₀]
      ring

/--
The precise assertion is `Nonempty (MomentWitness S u (S.V u t) theta)`.

Use: `chebyshev2.StateRegion.Scales.normalized_iff_attained` uses this assertion to
establish equivalence of the displayed criteria: `(u,v,theta) ∈ S.normalized ↔ Nonempty
(MomentWitness S u v theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.attain_thetaMinus`,
`chebyshev2.StateRegion.Scales.attain_thetaPlus`,
`chebyshev2.StateRegion.Scales.interval_mix` with the arguments shown in the proof.
-/
theorem attain_interval {u t theta : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (hθ : theta ∈ Icc (S.thetaMinus u t) (S.thetaPlus u t)) :
    Nonempty (MomentWitness S u (S.V u t) theta) := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.attain_thetaMinus`,
  -- `chebyshev2.StateRegion.Scales.attain_thetaPlus`,
  -- `chebyshev2.StateRegion.Scales.interval_mix` with the arguments shown in the proof.
  obtain ⟨L⟩ := S.attain_thetaMinus hu ht
  obtain ⟨H⟩ := S.attain_thetaPlus hu ht
  obtain ⟨l,hl,he⟩ := interval_mix hθ
  refine ⟨⟨mixture l L.measure H.measure,mixture_probability hl _ _,
    mixture_supported L.supported H.supported,?_,?_,?_⟩⟩
  · rw [mixture_integral hl (coord_integrable L.supported) (coord_integrable H.supported),L.mean,H.mean]
    ring
  · rw [mixture_integral hl (S.f_integrable L.supported) (S.f_integrable H.supported),L.second,H.second]
    ring
  · rw [mixture_integral hl (S.g_integrable L.supported) (S.g_integrable H.supported),he]
    linear_combination (1-l)*L.third+l*H.third

/--
Proposition 12 and Lemma 8: exact equality of the compact rational region and the three-moment
range, including all boundary faces and attainment.

Equivalence of the displayed criteria: `(u,v,theta) ∈ S.normalized ↔ Nonempty (MomentWitness S
u v theta)`.

Use: `chebyshev2.StateRegion.Scales.normalized_iff_original` uses this assertion to
establish equivalence of the displayed criteria: `(u,v,theta) ∈ S.normalized ↔ Nonempty
(S.OriginalWitness u v theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.attain_interval`,
`chebyshev2.StateRegion.Scales.moments_mem_normalized` with the arguments shown in the
proof.
-/
theorem normalized_iff_attained (u v theta : ℝ) :
    (u,v,theta) ∈ S.normalized ↔ Nonempty (MomentWitness S u v theta) := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.attain_interval`,
  -- `chebyshev2.StateRegion.Scales.moments_mem_normalized` with the arguments shown in the
  -- proof.
  constructor
  · rintro ⟨hu,t,ht,hv,hθ⟩
    dsimp only at hv hθ
    rw [hv]
    exact S.attain_interval hu ht hθ
  · rintro ⟨W⟩
    have h := S.moments_mem_normalized W.supported
    rw [W.mean,W.second,W.third] at h
    exact h

end Scales
end
end chebyshev2.StateRegion
