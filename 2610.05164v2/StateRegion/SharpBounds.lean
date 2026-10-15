import «2610.05164v2».StateRegion.Expectations
import «2610.05164v2».StateRegion.Compact

/-!
Article: 2610.05164v2, Proposition 7.
Every probability measure has its normalized moment triple in the compact region.
Use: `«2610.05164v2».StateRegion.Scales.moments_mem_normalized` feeds
`«2610.05164v2».StateRegion.Scales.normalized_iff_attained` (Proposition 12 and Lemma 8: exact
equality of the compact rational region and the three-moment range, including all boundary faces and
attainment).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».StateRegion.Scales
noncomputable section
open Set MeasureTheory
variable (S : Scales)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/--
Exact identity `S.D (S.yMinus u t)*S.V u t = S.k₀*u`.

Use: `«2610.05164v2».StateRegion.Scales.sharp_moment_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `1-(∫ w, S.g w ∂μ) ∈ Icc (S.thetaMinus
u t) (S.thetaPlus u t)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem yMinus_moment {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    S.D (S.yMinus u t)*S.V u t = S.k₀*u := by
  have ha := (S.k₀_pos.trans_le (S.yMinus_den_lower hu.2 ht.1)).ne'
  have hd := (S.D_pos hu.2).ne'
  simp only [D,yMinus,V,f]
  simp only [D,k₀,k₁] at ha hd ⊢
  field_simp [ha,hd]
  ring

/--
Exact identity `S.D (S.yPlus u t)*(1-S.V u t) = S.k₁*(1-u)`.

Use: `«2610.05164v2».StateRegion.Scales.sharp_moment_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `1-(∫ w, S.g w ∂μ) ∈ Icc (S.thetaMinus
u t) (S.thetaPlus u t)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem yPlus_moment {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    S.D (S.yPlus u t)*(1-S.V u t) = S.k₁*(1-u) := by
  have hb := (S.k₀_pos.trans_le (S.yPlus_den_lower hu ht)).ne'
  have hd := (S.D_pos hu.2).ne'
  simp only [D,yPlus,V,f]
  simp only [D,k₀,k₁] at hb hd ⊢
  field_simp [hb,hd]
  ring

/--
Exact identity `S.lowerB y*u+S.lowerC y*v=S.k₀*u/S.E y`.

Use: `«2610.05164v2».StateRegion.Scales.sharp_moment_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `1-(∫ w, S.g w ∂μ) ∈ Icc (S.thetaMinus
u t) (S.thetaPlus u t)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem lower_expected {u v y : ℝ} (hy : y ∈ Icc (0:ℝ) 1)
    (hv : S.D y*v=S.k₀*u) :
    S.lowerB y*u+S.lowerC y*v=S.k₀*u/S.E y := by
  have he := (S.E_pos hy.1).ne'
  simp only [lowerB,lowerC]
  field_simp [S.gap_pos.ne']
  dsimp [D,E,k₀,k₁,b] at hv ⊢
  linear_combination -S.a*(S.k+S.a+S.gap-S.gap*y)*hv

/--
Exact identity `1+S.upperB y*(u-1)+S.upperC y*(v-1)=1-S.k*(1-u)/S.E y`.

Use: `«2610.05164v2».StateRegion.Scales.sharp_moment_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `1-(∫ w, S.g w ∂μ) ∈ Icc (S.thetaMinus
u t) (S.thetaPlus u t)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem upper_expected {u v y : ℝ} (hy : y ∈ Icc (0:ℝ) 1)
    (hv : S.D y*(1-v)=S.k₁*(1-u)) :
    1+S.upperB y*(u-1)+S.upperC y*(v-1)=1-S.k*(1-u)/S.E y := by
  have he := (S.E_pos hy.1).ne'
  simp only [upperB,upperC]
  field_simp [S.gap_pos.ne',S.k₁_pos.ne']
  dsimp [D,E,k₀,k₁,b] at hv ⊢
  linear_combination S.k*S.a*(S.k+S.a+S.gap-S.gap*y)*hv

/--
Sharp three-moment bounds on the entire closed square, with all degenerate faces included.

Membership in the specified domain/enclosure: `1-(∫ w, S.g w ∂μ) ∈ Icc (S.thetaMinus u t)
(S.thetaPlus u t)`.

Use: `«2610.05164v2».StateRegion.Scales.moments_mem_normalized` uses this assertion to
establish membership in the specified domain/enclosure: `((∫ w, w ∂μ),(∫ w, S.f w ∂μ),1-(∫ w,
S.g w ∂μ)) ∈ S.normalized`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.yMinus_bounds`,
`«2610.05164v2».StateRegion.Scales.yPlus_bounds`,
`«2610.05164v2».StateRegion.Scales.third_moment_bounds` with the arguments shown in the proof.
-/
theorem sharp_moment_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) {u t : ℝ}
    (hu : u ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (hmean : (∫ w, w ∂μ)=u) (hf : (∫ w, S.f w ∂μ)=S.V u t) :
    1-(∫ w, S.g w ∂μ) ∈ Icc (S.thetaMinus u t) (S.thetaPlus u t) := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.yMinus_bounds`,
  -- `«2610.05164v2».StateRegion.Scales.yPlus_bounds`,
  -- `«2610.05164v2».StateRegion.Scales.third_moment_bounds` with the arguments shown in the
  -- proof.
  have hym : S.yMinus u t ∈ Icc (0:ℝ) 1 :=
    ⟨hu.1.trans (S.yMinus_bounds hu ht).1,(S.yMinus_bounds hu ht).2⟩
  have hyp : S.yPlus u t ∈ Icc (0:ℝ) 1 :=
    ⟨(S.yPlus_bounds hu ht).1,((S.yPlus_bounds hu ht).2).trans hu.2⟩
  obtain ⟨hl,hh⟩ := S.third_moment_bounds hμ hym hyp
  rw [hmean,hf,S.lower_expected hym (S.yMinus_moment hu ht)] at hl
  rw [hmean,hf,S.upper_expected hyp (S.yPlus_moment hu ht)] at hh
  constructor <;> dsimp [thetaMinus,thetaPlus] <;> linarith

/--
Constructs witnesses with the exact properties `∃ t ∈ Icc (0:ℝ) 1, v=S.V u t`.

Use: `«2610.05164v2».StateRegion.Scales.moments_mem_normalized` uses this identity to establish
membership in the specified domain/enclosure: `((∫ w, w ∂μ),(∫ w, S.f w ∂μ),1-(∫ w, S.g w ∂μ))
∈ S.normalized`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `S.f u=u` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem exists_moment_parameter {u v : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hv : v ∈ Icc (S.f u) u) : ∃ t ∈ Icc (0:ℝ) 1, v=S.V u t := by
  -- Separate `S.f u=u` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases he : S.f u=u
  · refine ⟨0,⟨le_rfl,zero_le_one⟩,?_⟩
    have h : v=S.f u := by linarith [hv.1,hv.2]
    simp [V,h]
  · have hp : 0 < u-S.f u := sub_pos.mpr (lt_of_le_of_ne (S.f_le_self hu) he)
    refine ⟨(v-S.f u)/(u-S.f u),⟨div_nonneg (sub_nonneg.mpr hv.1) hp.le,?_⟩,?_⟩
    · exact (div_le_one hp).mpr (by linarith [hv.2])
    · dsimp [V]
      field_simp
      ring

/--
Every probability measure has its normalized moment triple in the compact region. No operator
representation is assumed or hidden here.

Membership in the specified domain/enclosure: `((∫ w, w ∂μ),(∫ w, S.f w ∂μ),1-(∫ w, S.g w ∂μ))
∈ S.normalized`.

Use: `«2610.05164v2».StateRegion.Scales.normalized_iff_attained` uses this assertion to
establish equivalence of the displayed criteria: `(u,v,theta) ∈ S.normalized ↔ Nonempty
(MomentWitness S u v theta)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.mean_mem`,
`«2610.05164v2».StateRegion.Scales.exists_moment_parameter`,
`«2610.05164v2».StateRegion.Scales.two_moment_bounds` with the arguments shown in the proof.
-/
theorem moments_mem_normalized {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) :
    ((∫ w, w ∂μ),(∫ w, S.f w ∂μ),1-(∫ w, S.g w ∂μ)) ∈ S.normalized := by
  have hu := mean_mem hμ
  obtain ⟨t,ht,he⟩ := S.exists_moment_parameter hu (S.two_moment_bounds hμ)
  exact ⟨hu,t,ht,he,S.sharp_moment_bounds hμ hu ht rfl he⟩

end
end «2610.05164v2».StateRegion.Scales
