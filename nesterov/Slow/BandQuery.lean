import nesterov.Slow.Uniform
import nesterov.Slow.QueryDictionary
import nesterov.Slow.Forced

/-! Query normalization on a slow band, with a continuous extension away from
that band. The extension permits arbitrary probability measures and is equal
to the literal quotient wherever the query amplitude is bounded away from zero. -/
namespace nesterov.Slow
noncomputable section
open Spectral Filter Set MeasureTheory
open scoped Topology

def bandQueryPair (a : SymbolPair) : SymbolPair where
  u := 1
  p := ⟨fun x=>a.p x*star (a.u x)/((max (1/4) (Complex.normSq (a.u x)):ℝ):ℂ),by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (le_max_left _ _)))⟩

@[simp] theorem bandQueryPair_u (a : SymbolPair) (x : Frequency) : (bandQueryPair a).u x=1 := rfl

theorem bandQueryPair_p {a : SymbolPair} {x : Frequency}
    (hx : 1/4≤Complex.normSq (a.u x)) : (bandQueryPair a).p x=a.p x/a.u x := by
  change a.p x*star (a.u x)/((max (1/4) (Complex.normSq (a.u x)):ℝ):ℂ)=_
  rw [max_eq_right hx]
  have hu : a.u x≠0 := by intro h;rw [h,Complex.normSq_zero] at hx;norm_num at hx
  have hd : (Complex.normSq (a.u x):ℂ)≠0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hu).ne'
  apply (div_eq_div_iff hd hu).mpr
  rw [mul_assoc,Complex.star_def,mul_comm ((starRingEnd ℂ) (a.u x)) (a.u x),Complex.mul_conj]

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

/-- One endpoint neighborhood works for the entire compact slow band. -/
theorem query_band_defined {Ic : Set ℝ} (hIc : IsCompact Ic) {Γ : ℝ} (_hΓ : 0≤Γ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ c∈Ic,∀ γ∈Icc (0:ℝ) Γ,
      1/4≤Complex.normSq (((F.method ε).symbolPair (ε^2) 1 (-c*ε)).u (Phase.frequency (ε*γ))) := by
  let K := Ic ×ˢ Icc (0:ℝ) Γ
  have hK : IsCompact K := hIc.prod isCompact_Icc
  have him : IsCompact ((fun p : ℝ×ℝ=>slowPoint p.1 p.2) '' K) := hK.image (by unfold slowPoint;fun_prop)
  have hu := Metric.tendstoUniformlyOn_iff.mp (F.query_wave_uniform him) (1/2) (by norm_num)
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have heΓ : Tendsto (fun ε : ℝ=>ε*Γ) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using he.mul_const Γ
  have ht := heΓ.eventually (eventually_lt_nhds Real.pi_pos)
  filter_upwards [hu,ht,self_mem_nhdsWithin] with ε hε hπ heps c hc γ hγ
  have hω : ε*γ∈Icc (0:ℝ) Real.pi :=
    ⟨mul_nonneg heps.le hγ.1,((mul_le_mul_of_nonneg_left hγ.2 heps.le).trans_lt hπ).le⟩
  rw [F.sampled_query_value hω]
  have hn := hε (slowPoint c γ) ⟨(c,γ),⟨hc,hγ⟩,rfl⟩
  have hdiff : ‖(F.u ε).eval₂ Complex.ofRealHom (F.wave ε (slowPoint c γ))-(1:ℂ)‖<1/2 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hn
  have hrev := norm_add_le ((1:ℂ)-(F.u ε).eval₂ Complex.ofRealHom (F.wave ε (slowPoint c γ)))
    ((F.u ε).eval₂ Complex.ofRealHom (F.wave ε (slowPoint c γ)))
  rw [sub_add_cancel,norm_one,norm_sub_rev] at hrev
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg ((F.u ε).eval₂ Complex.ofRealHom (F.wave ε (slowPoint c γ)))]

/-- Lemma D.4 with the source order of quantifiers: the constant and endpoint
neighborhood precede the damping, measure, and feasible value charge. -/
theorem value_constant_forced {Ic : Set ℝ} (hIc : IsCompact Ic)
    (hIpos : Ic⊆Ioi (0:ℝ)) {Γ : ℝ} (hΓ : 0<Γ) :
    ∃ Kstar : ℝ,0≤Kstar ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ c∈Ic,
      ∀ (ν : Spectrum) (C : ℝ),
        (∀ᵐ (x : Frequency) ∂(ν : Measure Frequency),Real.arccos x≤ε*Γ) →
        Feasible (bandQueryPair ((F.method ε).symbolPair (ε^2) 1 (-c*ε))) (-c*ε) ν C →
        |C-measureCharge ν (bandQueryPair ((F.method ε).symbolPair (ε^2) 1 (-c*ε))) (-c*ε)|≤Kstar*ε^3 := by
  by_cases hne : Ic.Nonempty
  · obtain ⟨c₀,hc₀,hmin⟩ := hIc.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨c₁,hc₁,hmax⟩ := hIc.exists_isMaxOn hne continuous_id.continuousOn
    have hc₀p : 0<c₀ := hIpos hc₀
    have hc₁p : 0<c₁ := hIpos hc₁
    let K := Ic ×ˢ Icc (0:ℝ) Γ
    obtain ⟨B,hB,hbound⟩ := F.query_coefficients_uniform_bound (show IsCompact K from hIc.prod isCompact_Icc)
    have hdef := F.query_band_defined hIc hΓ.le
    have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 ∧ c₁*ε<1 ∧ Γ*ε<1 := by
      have h₁ := he.eventually (eventually_lt_nhds zero_lt_one)
      have h₂ : Tendsto (fun ε : ℝ=>c₁*ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using he.const_mul c₁
      have h₃ : Tendsto (fun ε : ℝ=>Γ*ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using he.const_mul Γ
      exact h₁.and ((h₂.eventually (eventually_lt_nhds zero_lt_one)).and
        (h₃.eventually (eventually_lt_nhds zero_lt_one)))
    refine ⟨(B*(c₁^2+Γ^2)+B*Γ*(c₁^2+Γ^2))/c₀,by positivity,?_⟩
    filter_upwards [hbound,hdef,hsmall,self_mem_nhdsWithin] with ε hb hd hs hε c hc ν C hband hfeas
    apply forced_on_band hfeas hε hs.1.le hc₀p (hmin hc) (hmax hc) hΓ.le hB.le hs.2.1.le hs.2.2.le hband
    filter_upwards [hband] with x hx
    let γ := Real.arccos x/ε
    have hγ : γ∈Icc (0:ℝ) Γ := ⟨div_nonneg (Real.arccos_nonneg _) hε.le,
      (div_le_iff₀ hε).mpr (by simpa only [mul_comm] using hx)⟩
    have heq : ε*γ=Real.arccos x := mul_div_cancel₀ _ hε.ne'
    have hω : ε*γ∈Icc (0:ℝ) Real.pi := by rw [heq];exact ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩
    have hfreq : Phase.frequency (ε*γ)=x := by
      apply Subtype.ext
      rw [heq]
      exact Real.cos_arccos x.2.1 x.2.2
    have hU := hd c hc γ hγ
    rw [hfreq] at hU
    have hUn : (((F.method ε).symbolPair (ε^2) 1 (-c*ε)).u x)≠0 := by
      intro hh
      rw [hh,Complex.normSq_zero] at hU
      norm_num at hU
    have hquery : (bandQueryPair ((F.method ε).symbolPair (ε^2) 1 (-c*ε))).p x=
        F.queryRatio ε (slowPoint c γ) := by
      rw [bandQueryPair_p hU,←hfreq]
      apply F.sampled_query_ratio hω (by have hh : 0<ε := hε; nlinarith [hs.1])
      rw [←F.sampled_query_value hω,hfreq]
      exact hUn
    have hh := hb (c,γ) ⟨hc,hγ⟩
    simpa only [g,skew,bandQueryPair_u,Complex.normSq_one,hquery,star_one,mul_one] using hh
  · refine ⟨0,le_rfl,Eventually.of_forall fun ε c hc=>?_⟩
    exact (hne ⟨c,hc⟩).elim

end SecondOrderFamily
end
end nesterov.Slow
