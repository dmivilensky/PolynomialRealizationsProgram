import chebyshev2.StateRegion.OriginalAttainment

/-!
Article: chebyshev2, Proposition 7.
The chord face has exactly the Bernoulli measure with the prescribed mean.
Result: `chebyshev2.StateRegion.Scales.upper_boundary_measure` supplies the stated article
conclusion.
-/
namespace chebyshev2.StateRegion.Scales
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
variable (S : Scales) {μ : Measure ℝ} [IsProbabilityMeasure μ]

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂μ, w=u`.

Use: `chebyshev2.StateRegion.Scales.lower_boundary_measure` uses this identity to establish
exact identity `μ=Measure.dirac u`.

Article: chebyshev2, Proposition 7 via
`chebyshev2.StateRegion.Scales.lower_boundary_measure`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem lower_boundary_ae {u : ℝ} (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1)
    (hm : (∫ w, w ∂μ)=u) (hf : (∫ w, S.f w ∂μ)=S.f u) : ∀ᵐ w ∂μ, w=u := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hu : u ∈ Icc (0:ℝ) 1 := hm ▸ mean_mem hμ
  let c := S.k₀*S.k₁/(S.D u)^2
  let T : ℝ → ℝ := fun w => S.f u+c*(w-u)
  have hi := coord_integrable hμ
  -- Establish ht as the integrability justification for the later integral estimates or
  -- changes of order.
  have ht : Integrable T μ := (integrable_const _).add ((hi.sub (integrable_const _)).const_mul _)
  have hti : (∫ w, T w ∂μ)=S.f u := by
    change (∫ w, S.f u+c*(w-u) ∂μ)=_
    calc
      _ = (∫ _ : ℝ, S.f u ∂μ)+(∫ w, c*(w-u) ∂μ) :=
        integral_add (integrable_const _) ((hi.sub (integrable_const _)).const_mul _)
      _ = S.f u+c*((∫ w : ℝ, w ∂μ)-u) := by
        rw [integral_const_mul]
        have he : (∫ w : ℝ, w-u ∂μ)=(∫ w : ℝ, w ∂μ)-u := by
          calc
            _ = (∫ w : ℝ, w ∂μ)-(∫ _ : ℝ, u ∂μ) := integral_sub hi (integrable_const _)
            _ = _ := by simp
        rw [he]
        simp
      _ = S.f u := by rw [hm]; ring
  have hn : ∀ᵐ w ∂μ, 0 ≤ S.f w-T w := hμ.mono (fun w hw => by
    have he := S.f_tangent_remainder hu hw
    change 0 ≤ S.f w-(S.f u+S.k₀*S.k₁/(S.D u)^2*(w-u))
    rw [he]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg S.k₀_pos.le S.k₁_pos.le)
      S.gap_pos.le) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (S.D_pos hw.2).le))
  have hz : (∫ w, S.f w-T w ∂μ)=0 := by
    rw [integral_sub (S.f_integrable hμ) ht,hf,hti,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn ((S.f_integrable hμ).sub ht)).mp hz
  filter_upwards [hμ,hae] with w hw he
  have hr := S.f_tangent_remainder hu hw
  change S.f w-(S.f u+S.k₀*S.k₁/(S.D u)^2*(w-u))=0 at he
  rw [he] at hr
  have hd : (S.D u)^2*S.D w ≠ 0 := mul_ne_zero (pow_ne_zero 2 (S.D_pos hu.2).ne') (S.D_pos hw.2).ne'
  have hnz := ((div_eq_zero_iff).mp hr.symm).resolve_right hd
  have hp : 0 < S.k₀*S.k₁*S.gap := mul_pos (mul_pos S.k₀_pos S.k₁_pos) S.gap_pos
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hnz).resolve_left hp.ne'))

/--
Exact identity `μ=Measure.dirac u`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Proposition 7.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.lower_boundary_ae` with
the arguments shown in the proof.
-/
theorem lower_boundary_measure {u : ℝ} (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1)
    (hm : (∫ w, w ∂μ)=u) (hf : (∫ w, S.f w ∂μ)=S.f u) : μ=Measure.dirac u := by
  have he : (fun w : ℝ => w) =ᵐ[μ] (fun _ => u) := S.lower_boundary_ae hμ hm hf
  have h : Measure.map id μ=Measure.map (fun _ : ℝ => u) μ := Measure.map_congr he
  simpa only [Measure.map_id,Measure.map_const,measure_univ,one_smul] using h

/--
Equality in the chord bound forces support on the two endpoints.

Establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂μ, w=0 ∨ w=1`.

Use: `chebyshev2.StateRegion.Scales.upper_boundary_measure` uses this identity to establish
exact identity `μ=twoPoint u 0 1`.

Article: chebyshev2, Proposition 7 via
`chebyshev2.StateRegion.Scales.upper_boundary_measure`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem upper_boundary_ae (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1)
    (hf : (∫ w, S.f w ∂μ)=(∫ w, w ∂μ)) : ∀ᵐ w ∂μ, w=0 ∨ w=1 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hi := (coord_integrable hμ).sub (S.f_integrable hμ)
  have hn : ∀ᵐ w ∂μ, 0 ≤ w-S.f w := hμ.mono (fun _ hw => sub_nonneg.mpr (S.f_le_self hw))
  have hz : (∫ w, w-S.f w ∂μ)=0 := by
    rw [integral_sub (coord_integrable hμ) (S.f_integrable hμ),hf,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  filter_upwards [hμ,hae] with w hw he
  have he' : S.f w=w := (sub_eq_zero.mp he).symm
  have hprod : w*(1-w)=0 := by
    rw [f,div_eq_iff (S.D_pos hw.2).ne'] at he'
    dsimp [D,k₀,k₁] at he'
    have hg := S.gap_pos.ne'
    apply (mul_eq_zero.mp (show S.gap*(w*(1-w))=0 by nlinarith only [he'])).resolve_left hg
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/--
The chord face has exactly the Bernoulli measure with the prescribed mean.

Exact identity `μ=twoPoint u 0 1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Proposition 7.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.upper_boundary_ae` with
the arguments shown in the proof.
-/
theorem upper_boundary_measure {u : ℝ} (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1)
    (hm : (∫ w, w ∂μ)=u) (hf : (∫ w, S.f w ∂μ)=u) : μ=twoPoint u 0 1 := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.upper_boundary_ae` with
  -- the arguments shown in the proof.
  have hs := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac (by norm_num : (0:ℝ) ≠ 1)).mp
    (S.upper_boundary_ae hμ (hf.trans hm.symm))
  have h0 : μ {0} ≠ ⊤ := measure_ne_top μ {0}
  have h1 : μ {1} ≠ ⊤ := measure_ne_top μ {1}
  -- Establish hi0 as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi0 : Integrable (fun w : ℝ => w) (μ {0} • Measure.dirac 0) :=
    (integrable_dirac (by finiteness)).smul_measure h0
  -- Establish hi1 as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi1 : Integrable (fun w : ℝ => w) (μ {1} • Measure.dirac 1) :=
    (integrable_dirac (by finiteness)).smul_measure h1
  have hi : (μ {1}).toReal=u := by
    have he := hm
    rw [hs,integral_add_measure hi0 hi1] at he
    simpa only [integral_smul_measure,integral_dirac,smul_eq_mul,mul_zero,mul_one,zero_add] using he
  have hmass : (μ {0}).toReal+(μ {1}).toReal=1 := by
    have he := congrArg ENNReal.toReal (congrArg (fun ν : Measure ℝ => ν univ) hs)
    simpa only [measure_univ,Measure.add_apply,Measure.smul_apply,smul_eq_mul,mul_one,
      ENNReal.toReal_one,ENNReal.toReal_add h0 h1] using he.symm
  have h0r : (μ {0}).toReal=1-u := by linarith
  have he0 : ENNReal.ofReal (1-u)=μ {0} := by rw [← h0r,ENNReal.ofReal_toReal h0]
  have he1 : ENNReal.ofReal u=μ {1} := by rw [← hi,ENNReal.ofReal_toReal h1]
  rw [twoPoint,mixture,he0,he1]
  exact hs

end
end chebyshev2.StateRegion.Scales
